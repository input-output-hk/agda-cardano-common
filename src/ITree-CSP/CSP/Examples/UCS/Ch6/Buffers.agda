{-# OPTIONS --guardedness #-}

-- UCS chapter 6: buffers (buffers.csp, Bill Roscoe). FD buffer hierarchy, T = Bool.
--   BUFFN(N,<>) = left?x -> BUFFN(N,<x>)
--   BUFFN(N,s)  = right!head(s) -> BUFFN(N,tail(s))
--                 [] #s<N & (STOP |~| left?x -> BUFFN(N,s^<x>))
--   COPY = left?x -> right!x -> COPY
-- The `STOP |~| left?…` internal choice under `[]` is modelled as a FUSED sliding
-- node: a not-full non-empty state offers `right!head` visibly AND has two τ-branches
-- — one to a deadlock-on-accept state (offers `right` only) and one to an accept
-- state (offers `right` and `left`).  Deferred (non-goals): WBUFF, chaining
-- (link-parallel [right<->left]), N>2, the full assert list.

module CSP.Examples.UCS.Ch6.Buffers where

open import Level using (lift; Lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using () renaming (_<?_ to _ℕ<?_)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; length)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
-- §2. COPY (PINNED output).
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

------------------------------------------------------------------------------------
-- §3. The most-nondeterministic bounded buffer BUFN + its fused sliding node.
--   BUFN n []       : accept left only (deterministic).
--   BUFN n (x ∷ cs) : FULL      → right!x only, stable.
--                     NOT FULL  → fused sliding node: visible right!x AND
--                                 τ-branches to Bstop (STOP-resolved) / Baccept
--                                 (accept-resolved).
BUFN    : ℕ → List Bool → BProc
Bstop   : ℕ → Bool → List Bool → BProc   -- STOP-resolved: right!x only
Baccept : ℕ → Bool → List Bool → BProc   -- accept-resolved: right!x AND left?y

-- empty: accept left only
force (BUFN n []) = react
  (λ where (_ , left) x → just (BUFN n (x ∷ []))
           (_ , right) _ → nothing)
  ∅t
-- non-empty: split on full / not-full
force (BUFN n (x ∷ cs)) with length (x ∷ cs) ℕ<? n
... | no  _ = react   -- FULL: right!x only, stable
      (λ where (_ , right) y → case y B≟ x of λ where (yes _) → just (BUFN n cs) ; (no _) → nothing
               (_ , left) _ → nothing)
      ∅t
... | yes _ = react   -- NOT FULL: fused sliding node — visible right!x + τ to Bstop / Baccept
      (λ where (_ , right) y → case y B≟ x of λ where (yes _) → just (BUFN n cs) ; (no _) → nothing
               (_ , left) _ → nothing)
      (λ where (_ , fin) (lift fzero)              → just (Bstop n x cs)
               (_ , fin) (lift (fsuc fzero))        → just (Baccept n x cs)
               (_ , fin) (lift (fsuc (fsuc _)))     → nothing
               (_ , base _) _                       → nothing
               (_ , pair _ _) _                      → nothing)

-- Bstop n x cs: offers right!x only (the STOP branch keeps right available, refuses left)
force (Bstop n x cs) = react
  (λ where (_ , right) y → case y B≟ x of λ where (yes _) → just (BUFN n cs) ; (no _) → nothing
           (_ , left) _ → nothing)
  ∅t
-- Baccept n x cs: offers right!x AND left?y (accept a second item)
force (Baccept n x cs) = react
  (λ where (_ , right) y → case y B≟ x of λ where (yes _) → just (BUFN n cs) ; (no _) → nothing
           (_ , left) y → just (BUFN n ((x ∷ cs) ∷ʳ y)))
  ∅t

BUFFN1 BUFFN2 : BProc
BUFFN1 = BUFN 1 []
BUFFN2 = BUFN 2 []

------------------------------------------------------------------------------------
-- §B. COPY is the one-place buffer:  BUFFN1 ≈FD COPY.
--
--   BUFFN1 = BUFN 1 [] reduces to the COPY loop.  BUFN 1 [] offers `left?x`;
--   BUFN 1 (x ∷ []) is FULL (¬ (1 < 1)) so offers only the PINNED `right!x`.
--   So the reachable states are a 2-state correspondence
--       BUFN 1 []       ↔ COPY
--       BUFN 1 (x ∷ []) ↔ COPYout x
--   with identical offers, both stable (react … ∅t), neither diverging.
--
--   ROUTE: the (recommended) BRIDGE route.  We build a divergence-respecting
--   weak bisimulation `≈DR` over the 2 states via `DRFromRel` (both processes
--   are τ-free, so the two divergence obligations of `DRFromRel` are vacuous),
--   then apply `drbisim→≈FD`.  This inherits the ONE certified classical
--   postulate of the development, `¬-divergent→normal` (in
--   `Semantics.DRImpliesFD`, used inside `drbisim→⊑F⊥`), as the chapter 1-3 FD
--   results do.  §B itself contains no postulate / NON_TERMINATING / mutual.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂)

-- `Diverges` is hidden here because `Semantics.DRBisim` re-exports the very same LTS
-- `Diverges`; importing both unqualified would make the name ambiguous.
open import Semantics.LTS       {E = BEv} {I = ExtI BEv} hiding (Diverges)
open import Semantics.WeakBisim {E = BEv} {I = ExtI BEv}
  using (_═[_]═►_; wev; τ*-refl)
open import Semantics.DRBisim   {E = BEv} {I = ExtI BEv} using (Diverges; _≈DR_)
open import Semantics.DRImpliesFD {E = BEv} {I = ExtI BEv} using (drbisim→≈FD)
open import Semantics.FailuresDivergences {E = BEv} {I = ExtI BEv} using (_≈FD_)
open import Semantics.BisimFromRel {E = BEv} {I = ExtI BEv}

-- The 2-state correspondence relation.
data BRel : BProc → BProc → Set where
  rel-empty : BRel (BUFN 1 []) COPY
  rel-full  : ∀ x → BRel (BUFN 1 (x ∷ [])) (COPYout x)

-- Concrete single strong steps of the four states (input on `left`, output the
-- PINNED value on `right`).  The output fires need a `y ≡ x` witness so the
-- payload decision `y B≟ x` reduces to the `yes` branch.
copy-in-fire : ∀ x → COPY ─[ ev (evl (evLabel Bool left x)) ]─► COPYout x
copy-in-fire x = sVis {at = Bool , left} {a = x} refl refl

bufn-in-fire : ∀ x → BUFN 1 [] ─[ ev (evl (evLabel Bool left x)) ]─► BUFN 1 (x ∷ [])
bufn-in-fire x = sVis {at = Bool , left} {a = x} refl refl

-- Casing on the concrete Bool makes the payload decision `x B≟ x` reduce to
-- `yes refl`, so the node's *own* offer lambda computes (restating the lambda
-- would give a distinct extended-lambda, hence unequal, term).
copyout-fire : ∀ x {y} → y ≡ x → COPYout x ─[ ev (evl (evLabel Bool right y)) ]─► COPY
copyout-fire x refl = go x
  where go : ∀ x → COPYout x ─[ ev (evl (evLabel Bool right x)) ]─► COPY
        go true  = sVis {at = Bool , right} {a = true}  refl refl
        go false = sVis {at = Bool , right} {a = false} refl refl

bufn-out-fire : ∀ x {y} → y ≡ x
              → BUFN 1 (x ∷ []) ─[ ev (evl (evLabel Bool right y)) ]─► BUFN 1 []
bufn-out-fire x refl = go x
  where go : ∀ x → BUFN 1 (x ∷ []) ─[ ev (evl (evLabel Bool right x)) ]─► BUFN 1 []
        go true  = sVis {at = Bool , right} {a = true}  refl refl
        go false = sVis {at = Bool , right} {a = false} refl refl

-- τ-freeness of both sides (react … ∅t: no `sil`, and `∅t i a = nothing`).
noτ-L : ∀ {p q} → BRel p q → ∀ {p′} → p ─[ τ ]─► p′ → ⊥
noτ-L rel-empty    (sSil ())
noτ-L rel-empty    (sTau refl ())
noτ-L (rel-full x) (sSil ())
noτ-L (rel-full x) (sTau refl ())

noτ-R : ∀ {p q} → BRel p q → ∀ {q′} → q ─[ τ ]─► q′ → ⊥
noτ-R rel-empty    (sSil ())
noτ-R rel-empty    (sTau refl ())
noτ-R (rel-full x) (sSil ())
noτ-R (rel-full x) (sTau refl ())

-- The `DRFromRel` obligations.
fwdE : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′} → BRel p q → p ─[ ev l ]─► p′
     → Σ[ q′ ∈ BProc ] ((q ═[ ev l ]═► q′) × BRel p′ q′)
fwdE rel-empty (sRet ())
fwdE rel-empty (sVis {at = _ , left}  {a = x} refl br) =
  case br of λ { refl → COPYout x , wev τ*-refl (copy-in-fire x) τ*-refl , rel-full x }
fwdE rel-empty (sVis {at = _ , right} refl br) = case br of λ ()
fwdE (rel-full x) (sRet ())
fwdE (rel-full x) (sVis {at = _ , left}  refl br) = case br of λ ()
fwdE (rel-full x) (sVis {at = _ , right} {a = y} refl br) with y B≟ x
... | yes e  = case br of λ { refl → COPY , wev τ*-refl (copyout-fire x e) τ*-refl , rel-empty }
... | no ¬p  = case br of λ ()

bwdE : ∀ {p q} {l : Event√ (⊤poly {lzero})} {q′} → BRel p q → q ─[ ev l ]─► q′
     → Σ[ p′ ∈ BProc ] ((p ═[ ev l ]═► p′) × BRel p′ q′)
bwdE rel-empty (sRet ())
bwdE rel-empty (sVis {at = _ , left}  {a = x} refl br) =
  case br of λ { refl → BUFN 1 (x ∷ []) , wev τ*-refl (bufn-in-fire x) τ*-refl , rel-full x }
bwdE rel-empty (sVis {at = _ , right} refl br) = case br of λ ()
bwdE (rel-full x) (sRet ())
bwdE (rel-full x) (sVis {at = _ , left}  refl br) = case br of λ ()
bwdE (rel-full x) (sVis {at = _ , right} {a = y} refl br) with y B≟ x
... | yes e  = case br of λ { refl → BUFN 1 [] , wev τ*-refl (bufn-out-fire x e) τ*-refl , rel-empty }
... | no ¬p  = case br of λ ()

fwdT : ∀ {p q p′} → BRel p q → p ─[ τ ]─► p′
     → Σ[ q′ ∈ BProc ] ((q ═[ τ ]═► q′) × BRel p′ q′)
fwdT r pτ = ⊥-elim (noτ-L r pτ)

bwdT : ∀ {p q q′} → BRel p q → q ─[ τ ]─► q′
     → Σ[ p′ ∈ BProc ] ((p ═[ τ ]═► p′) × BRel p′ q′)
bwdT r qτ = ⊥-elim (noτ-R r qτ)

ndivL : ∀ {p q} → BRel p q → Diverges p → ⊥
ndivL r d = noτ-L r (d .Diverges.step)

ndivR : ∀ {p q} → BRel p q → Diverges q → ⊥
ndivR r d = noτ-R r (d .Diverges.step)

open DRFromRel BRel fwdE fwdT bwdE bwdT ndivL ndivR

buff1≈DR-copy : BUFN 1 [] ≈DR COPY
buff1≈DR-copy = rel→dr rel-empty

copy-is-buff1 : BUFFN1 ≈FD COPY
copy-is-buff1 = drbisim→≈FD buff1≈DR-copy

------------------------------------------------------------------------------------
-- §C. Buffer size is FD-observable:  ¬ (BUFFN1 ⊑FD BUFFN2).
--
--   BUFFN2 = BUFN 2 [] can hold TWO items: it has the visible trace
--   sₐ = [left true, left false] reaching the STABLE full state BUFN 2 [true,false]
--   (offers only right!true), giving a stable failure — a `failures⊥ BUFFN2 sₐ B`
--   for any refusal B (we take B = ⊥, refused by every stable state).
--
--   BUFFN1 = BUFN 1 [] can hold only ONE item: after `left true` it is the FULL
--   state BUFN 1 [true] (offers only right!true), so the second `left false` cannot
--   fire — BUFFN1 has NO trace sₐ — and BUFFN1 never diverges (every reachable state
--   is `react … ∅t`, τ-free).  So `failures⊥ BUFFN1 sₐ B` is empty and the ⊑F⊥
--   component of any `BUFFN1 ⊑FD BUFFN2` is refuted.  This is a DIRECT existential
--   refutation: no FD bridge / DRbisim, POSTULATE-FREE.

open import Data.Sum using (inj₁; inj₂)
open import Semantics.Failures            {E = BEv} {I = ExtI BEv}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.Refusals            {E = BEv} {I = ExtI BEv} using (Refuses; Offers)
open import Semantics.FailuresDivergences {E = BEv} {I = ExtI BEv}
  using (_⊑FD_; _⊑F⊥_; _⊑D_; failures⊥; divergences; IsDivergence)

-- The size-2 witness trace and the (⊥) refusal.
sₐ : List (Event√ (⊤poly {lzero}))
sₐ = evl (evLabel Bool left true) ∷ evl (evLabel Bool left false) ∷ []

Bset : Event√ (⊤poly {lzero}) → Set lzero
Bset _ = ⊥

BFull : BProc
BFull = BUFN 2 (true ∷ false ∷ [])

-- BUFFN2 reaches the stable full state along sₐ:
--   BUFN 2 [] ─[left true]─► BUFN 2 [true] ─[τ: accept]─► Baccept 2 true []
--             ─[left false]─► BUFN 2 [true,false]  (FULL, stable).
buff2-tr : BUFFN2 ⟹⟨ sₐ ⟩ BFull
buff2-tr =
  ⟹-ev (sVis {at = _ , left} {a = true} refl refl)
 (⟹-τ  (sTau {i = Lift lzero (Fin (suc (suc zero))) , fin} {a = lift (fsuc fzero)} refl refl)
 (⟹-ev (sVis {at = _ , left} {a = false} refl refl)
  ⟹-refl))

-- The full state is stable and (vacuously) refuses ⊥.
buff2-ref : Refuses BFull Bset
buff2-ref = (λ _ _ → refl) , (λ e ())

-- BUFFN2's stable failure at sₐ.
f2 : failures⊥ BUFFN2 sₐ Bset
f2 = inj₁ (BFull , buff2-tr , buff2-ref)

-- The BUFFN1-reachable states: the empty state and the one FULL state.  Both τ-free.
data B1Reach : BProc → Set where
  at-empty : B1Reach (BUFN 1 [])
  at-full  : ∀ x → B1Reach (BUFN 1 (x ∷ []))

b1-noτ : ∀ {W W′} → B1Reach W → ¬ (W ─[ τ ]─► W′)
b1-noτ at-empty    (sSil ())
b1-noτ at-empty    (sTau refl ())
b1-noτ (at-full x) (sSil ())
b1-noτ (at-full x) (sTau refl ())

b1-step-stays : ∀ {W W′} {e : Event√ (⊤poly {lzero})}
              → B1Reach W → W ─[ ev e ]─► W′ → B1Reach W′
b1-step-stays at-empty    (sRet ())
b1-step-stays at-empty    (sVis {at = _ , left}  {a = x} refl refl) = at-full x
b1-step-stays at-empty    (sVis {at = _ , right} refl ())
b1-step-stays (at-full x) (sRet ())
b1-step-stays (at-full x) (sVis {at = _ , left}  refl ())
b1-step-stays (at-full x) (sVis {at = _ , right} {a = y} refl br) with y B≟ x
... | yes _ = case br of λ { refl → at-empty }
... | no  _ = case br of λ ()

reach→B1 : ∀ {V s W} → B1Reach V → V ⟹⟨ s ⟩ W → B1Reach W
reach→B1 bv ⟹-refl         = bv
reach→B1 bv (⟹-τ  pτ _)    = ⊥-elim (b1-noτ bv pτ)
reach→B1 bv (⟹-ev st rest) = reach→B1 (b1-step-stays bv st) rest

-- BUFFN1 has no `[left true, left false]` trace: after `left true` it is the FULL
-- state BUFN 1 [true], which offers only `right`, so the second `left` cannot fire.
buff1-no-sₐ : ∀ {W} → BUFN 1 [] ⟹⟨ sₐ ⟩ W → ⊥
buff1-no-sₐ (⟹-τ pτ _) = b1-noτ at-empty pτ
buff1-no-sₐ (⟹-ev (sVis {at = _ , left} refl refl) rest) = inner rest
  where
    inner : ∀ {W} → BUFN 1 (true ∷ []) ⟹⟨ evl (evLabel Bool left false) ∷ [] ⟩ W → ⊥
    inner (⟹-τ pτ _) = b1-noτ (at-full true) pτ
    inner (⟹-ev (sVis {at = _ , left} refl ()) _)

-- BUFFN1 never diverges: every reachable state is τ-free.
div-absurd : divergences BUFFN1 sₐ → ⊥
div-absurd d =
  b1-noτ (reach→B1 at-empty (d .IsDivergence.reach))
         (d .IsDivergence.divwit .Diverges.step)

-- Feeding BUFFN2's stable size-2 failure to the ⊑F⊥ component demands the same of
-- BUFFN1 — impossible on both disjuncts (no trace, no divergence).
¬buff1⊑buff2 : ¬ (BUFFN1 ⊑FD BUFFN2)
¬buff1⊑buff2 (h⊥ , _) with h⊥ f2
... | inj₁ (_ , reach , _) = buff1-no-sₐ reach
... | inj₂ d               = div-absurd d

------------------------------------------------------------------------------------
-- §D. The buffer size hierarchy (universal):  BUFFN2 ⊑FD BUFFN1.
--
--   A SMALLER buffer refines a BIGGER one — every failure/divergence of BUFFN1 is
--   one of BUFFN2.  ⊑D is vacuous (BUFFN1 is divergence-free, §C).  For ⊑F⊥ we set
--   up a state correspondence between the two BUFFN1-reachable states and matching
--   BUFFN2 states with IDENTICAL stable offers/refusals:
--       BUFN 1 []       ↔ BUFN 2 []      (both offer `left` only)
--       BUFN 1 (x ∷ []) ↔ Bstop 2 x []  (both offer `right x` only, refuse `left`)
--   The crux: BUFFN2 reproduces BUFFN1's FULL/refuse-`left` behaviour precisely via
--   the STOP branch of its sliding node — reached by the τ-slide
--       BUFN 2 (x ∷ []) ─[τ: fzero]─► Bstop 2 x [] .
--   A visible step on either side keeps the correspondence, so any BUFFN1 trace lifts
--   to a BUFFN2 trace reaching a corresponding (identically-refusing) state.  DIRECT
--   (no drbisim / FD bridge); the only inherited postulate is the same certified one
--   the §B / chapter FD results carry (none is added here).

-- The 2-state correspondence between BUFFN1- and BUFFN2-reachable states.
data BCorr : BProc → BProc → Set where
  bc-empty : BCorr (BUFN 1 []) (BUFN 2 [])
  bc-full  : ∀ x → BCorr (BUFN 1 (x ∷ [])) (Bstop 2 x [])

bcorr→b1 : ∀ {P Q} → BCorr P Q → B1Reach P
bcorr→b1 bc-empty    = at-empty
bcorr→b1 (bc-full x) = at-full x

-- The BUFFN2 side of the correspondence is stable (react … ∅t).
bcorr-stableQ : ∀ {P Q} → BCorr P Q → isStable Q
bcorr-stableQ bc-empty    _ _ = refl
bcorr-stableQ (bc-full x) _ _ = refl

-- BUFFN1 has no divergence at ALL (generalises §C's div-absurd to arbitrary s).
buff1-nodiv : ∀ {s} → divergences BUFFN1 s → ⊥
buff1-nodiv d =
  b1-noτ (reach→B1 at-empty (d .IsDivergence.reach))
         (d .IsDivergence.divwit .Diverges.step)

-- Concatenation of visible big-steps (needed to prepend a single lifted event).
⟹-++ : ∀ {V W Z : BProc} {s t} → V ⟹⟨ s ⟩ W → W ⟹⟨ t ⟩ Z → V ⟹⟨ s ++ t ⟩ Z
⟹-++ ⟹-refl         w = w
⟹-++ (⟹-τ  pτ rest) w = ⟹-τ  pτ (⟹-++ rest w)
⟹-++ (⟹-ev st rest) w = ⟹-ev st (⟹-++ rest w)

-- The τ-slide witness:  BUFN 2 (x ∷ []) ─[τ: fzero]─► Bstop 2 x []  (the STOP branch).
buff2-slide-stop : ∀ x → BUFN 2 (x ∷ []) ─[ τ ]─► Bstop 2 x []
buff2-slide-stop x =
  sTau {i = Lift lzero (Fin (suc (suc zero))) , fin} {a = lift fzero} refl refl

-- The BUFFN2 input step (empty → not-full sliding node).
buff2-in-fire : ∀ x → BUFN 2 [] ─[ ev (evl (evLabel Bool left x)) ]─► BUFN 2 (x ∷ [])
buff2-in-fire x = sVis {at = Bool , left} {a = x} refl refl

-- The Bstop output step (pinned right!x back to the empty size-2 state).
bstop-out-fire : ∀ x {y} → y ≡ x
               → Bstop 2 x [] ─[ ev (evl (evLabel Bool right y)) ]─► BUFN 2 []
bstop-out-fire x refl = go x
  where go : ∀ x → Bstop 2 x [] ─[ ev (evl (evLabel Bool right x)) ]─► BUFN 2 []
        go true  = sVis {at = Bool , right} {a = true}  refl refl
        go false = sVis {at = Bool , right} {a = false} refl refl

-- Offer reflection: every visible offer of the BUFFN2 side is matched by the BUFFN1
-- side (so any refusal transports from BUFFN1 to BUFFN2).
bcorr-reflect : ∀ {P Q} {e : Event√ (⊤poly {lzero})}
              → BCorr P Q → Offers Q e → Offers P e
bcorr-reflect bc-empty    (_ , sRet ())
bcorr-reflect bc-empty    (_ , sVis {at = _ , right} refl ())
bcorr-reflect bc-empty    (_ , sVis {at = _ , left} {a = x} refl refl) =
  BUFN 1 (x ∷ []) , sVis {at = Bool , left} {a = x} refl refl
bcorr-reflect (bc-full x) (_ , sRet ())
bcorr-reflect (bc-full x) (_ , sVis {at = _ , left} refl ())
bcorr-reflect (bc-full x) (_ , sVis {at = _ , right} {a = y} refl br) with y B≟ x
... | yes e = BUFN 1 [] , bufn-out-fire x e
... | no  _ = case br of λ ()

-- Refusal transport across the correspondence.
bcorr-refuse : ∀ {ℓx} {P Q} {B : Event√ (⊤poly {lzero}) → Set ℓx}
             → BCorr P Q → Refuses P B → Refuses Q B
bcorr-refuse c (_ , noOff) =
  bcorr-stableQ c , λ e be off → noOff e be (bcorr-reflect c off)

-- Single visible step lifts across the correspondence (with the τ-slide on the
-- BUFFN2 side when moving to the FULL/STOP state).
bcorr-step : ∀ {P Q P₁} {e : Event√ (⊤poly {lzero})}
           → BCorr P Q → P ─[ ev e ]─► P₁
           → Σ[ Q₁ ∈ BProc ] ((Q ⟹⟨ e ∷ [] ⟩ Q₁) × BCorr P₁ Q₁)
bcorr-step bc-empty (sRet ())
bcorr-step bc-empty (sVis {at = _ , right} refl ())
bcorr-step bc-empty (sVis {at = _ , left} {a = x} refl br) = case br of λ where
  refl → Bstop 2 x [] , ⟹-ev (buff2-in-fire x) (⟹-τ (buff2-slide-stop x) ⟹-refl) , bc-full x
bcorr-step (bc-full x) (sRet ())
bcorr-step (bc-full x) (sVis {at = _ , left} refl ())
bcorr-step (bc-full x) (sVis {at = _ , right} {a = y} refl br) with y B≟ x
... | yes e = case br of λ where
  refl → BUFN 2 [] , ⟹-ev (bstop-out-fire x e) ⟹-refl , bc-empty
... | no  _ = case br of λ ()

-- Trace simulation: a BUFFN1 trace lifts to a BUFFN2 trace ending in a corresponding
-- (identically-refusing) state.  τ-steps on the BUFFN1 side are impossible (§C).
bcorr-sim : ∀ {P Q s P′} → BCorr P Q → P ⟹⟨ s ⟩ P′
          → Σ[ Q′ ∈ BProc ] ((Q ⟹⟨ s ⟩ Q′) × BCorr P′ Q′)
bcorr-sim c ⟹-refl         = _ , ⟹-refl , c
bcorr-sim c (⟹-τ  pτ _)    = ⊥-elim (b1-noτ (bcorr→b1 c) pτ)
bcorr-sim c (⟹-ev st rest) with bcorr-step c st
... | Q₁ , qtr , c₁ with bcorr-sim c₁ rest
...   | Q′ , qtr′ , c′ = Q′ , ⟹-++ qtr qtr′ , c′

-- The size hierarchy.  ⊑F⊥: every BUFFN1 failure maps to a BUFFN2 failure at the same
-- trace/refusal (divergence disjunct impossible).  ⊑D: vacuous (BUFFN1 has no div).
buff2⊑buff1 : BUFFN2 ⊑FD BUFFN1
buff2⊑buff1 = f⊥ , fD
  where
    f⊥ : BUFFN2 ⊑F⊥ BUFFN1
    f⊥ (inj₁ (P′ , tr , ref)) with bcorr-sim bc-empty tr
    ... | Q′ , qtr , c′ = inj₁ (Q′ , qtr , bcorr-refuse c′ ref)
    f⊥ (inj₂ d) = ⊥-elim (buff1-nodiv d)

    fD : BUFFN2 ⊑D BUFFN1
    fD d = ⊥-elim (buff1-nodiv d)
