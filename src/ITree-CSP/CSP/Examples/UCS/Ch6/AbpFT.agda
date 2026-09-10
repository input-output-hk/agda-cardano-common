{-# OPTIONS --guardedness #-}

-- UCS chapter 6: abp-ft (abp-ft.csp, Bill Roscoe) — fault tolerance via LAZY
-- ABSTRACTION (§6.5), at the single-channel level.  T = Bool (data-independent
-- reduction of TAG.DATA).
--   COPY(in,out) = in?x -> out!x -> COPY
--   CE(in,out)   = in?x -> (out!x -> CE'(x) [] lose -> CE)          -- controlled error
--   CE'(x)       = (dup -> out!x -> CE'(x)) [] CE                   -- may duplicate/accept
--   C(in,out)    = in?x -> C'(x) ; C'(x) = (out!x -> C'(x)) |~| (in?y -> C'(y))  -- lossy medium
--   Errors = {lose,dup} ; CHAOS(X) = STOP |~| ([] e:X -> CHAOS(X))
--   LAbs(X)(P)   = (P [|X|] CHAOS(X)) \ X                           -- normal(…) = identity, omitted
-- Channel-level asserts ported:
--   COPY(a,b) [FD= CE(a,b) [|Errors|] STOP      -- errors-off ⇒ reliable buffer  (PROVED, §B)
--   C(a,b) [F= LAbs(Errors)(CE(a,b))  (both dirs) -- abstraction ⇒ lossy medium  (DEFERRED, §C:
--     the LAbsE-CE step/τ characterisation is proved; the two-way ≈F equivalence is not —
--     it is a failures-level union over runs, not a forward simulation; see §C header.)
-- DEFERRED (non-goals): the full SYSTEME/SYSTEMA (SEND/RCVimp/E/F) refinements
-- (COPY/NoError [F= SYSTEMA — the plain-ABP 594-state closure wall + abstraction);
-- normal compression; larger DATA/TAG.

module CSP.Examples.UCS.Ch6.AbpFT where

open import Level using (lift; Lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §1. The event type and its decidable equality.
--   cin/cout : the single channel, in/out, carries a DATA value (Bool).
--   lose/dup : the controlled-error events (no payload).
data CEv : Set → Set where
  cin cout : CEv Bool
  lose dup : CEv ⊤

CEv-≟ : (x y : AnyTypes CEv) → Dec (x ≡ y)
CEv-≟ (_ , cin)  (_ , cin)  = yes refl
CEv-≟ (_ , cout) (_ , cout) = yes refl
CEv-≟ (_ , lose) (_ , lose) = yes refl
CEv-≟ (_ , dup)  (_ , dup)  = yes refl
CEv-≟ (_ , cin)  (_ , cout) = no (λ ())
CEv-≟ (_ , cin)  (_ , lose) = no (λ ())
CEv-≟ (_ , cin)  (_ , dup)  = no (λ ())
CEv-≟ (_ , cout) (_ , cin)  = no (λ ())
CEv-≟ (_ , cout) (_ , lose) = no (λ ())
CEv-≟ (_ , cout) (_ , dup)  = no (λ ())
CEv-≟ (_ , lose) (_ , cin)  = no (λ ())
CEv-≟ (_ , lose) (_ , cout) = no (λ ())
CEv-≟ (_ , lose) (_ , dup)  = no (λ ())
CEv-≟ (_ , dup)  (_ , cin)  = no (λ ())
CEv-≟ (_ , dup)  (_ , cout) = no (λ ())
CEv-≟ (_ , dup)  (_ , lose) = no (λ ())

open import CSP.Operators CEv-≟
open EventSet

CProc : Set₁
CProc = PTree CEv (ExtI CEv) (⊤poly {lzero})

------------------------------------------------------------------------------------
-- §2. COPY (PINNED output).
--   COPY(in,out) = in?x -> out!x -> COPY
COPY    : CProc
COPYout : Bool → CProc

force COPY = react
  (λ where (_ , cin) x → just (COPYout x)
           (_ , cout) _ → nothing ; (_ , lose) _ → nothing ; (_ , dup) _ → nothing)
  ∅t
force (COPYout x) = react
  (λ where (_ , cout) y → case y B≟ x of λ where (yes _) → just COPY ; (no _) → nothing
           (_ , cin) _ → nothing ; (_ , lose) _ → nothing ; (_ , dup) _ → nothing)
  ∅t

------------------------------------------------------------------------------------
-- §3. The controlled-error channel CE (4 states, PINNED output).
--   CE(in,out)   = in?x -> (out!x -> CE'(x) [] lose -> CE)
--   CE'(x)       = (dup -> out!x -> CE'(x)) [] CE
-- `CE` accepts and moves to `CEmid x` (output-or-lose); `CEmid x` either produces
-- the PINNED `cout!x` and moves to `CE' x`, or `lose`s back to `CE`.  `CE' x`
-- offers `dup` (→ `CEdup x`, the duplicated output) AND re-embeds `CE`'s own
-- `cin?y` arm (since `CE` offers only `cin`, that is exactly the `[] CE` clause).
CE    : CProc              -- cin?x → CEmid x
CEmid : Bool → CProc       -- cout!x → CE' x   □  lose → CE
CE'   : Bool → CProc       -- dup → CEdup x    □  (CE : cin?y → CEmid y)
CEdup : Bool → CProc       -- cout!x → CE' x   (the duplicated output)

force CE = react
  (λ where (_ , cin) x → just (CEmid x)
           (_ , cout) _ → nothing ; (_ , lose) _ → nothing ; (_ , dup) _ → nothing)
  ∅t
force (CEmid x) = react
  (λ where (_ , cout) y → case y B≟ x of λ where (yes _) → just (CE' x) ; (no _) → nothing
           (_ , lose) _ → just CE
           (_ , cin) _ → nothing ; (_ , dup) _ → nothing)
  ∅t
force (CE' x) = react
  (λ where (_ , dup) _ → just (CEdup x)
           (_ , cin) y → just (CEmid y)               -- the `[] CE` re-embedding (CE offers only cin)
           (_ , cout) _ → nothing ; (_ , lose) _ → nothing)
  ∅t
force (CEdup x) = react
  (λ where (_ , cout) y → case y B≟ x of λ where (yes _) → just (CE' x) ; (no _) → nothing
           (_ , cin) _ → nothing ; (_ , lose) _ → nothing ; (_ , dup) _ → nothing)
  ∅t

------------------------------------------------------------------------------------
-- §4. The lossy medium C (`⊓` inlined).
--   C(in,out) = in?x -> C'(x)
--   C'(x)     = (out!x -> C'(x)) |~| (in?y -> C'(y))
-- `C' x` is an internal choice (no visible offers of its own, `react ∅v`) between
-- re-outputting the held value (`Cout x`) and being silently overwritten by a
-- fresh input (`Cacc x`) — the same inlined-`⊓` shape as `BElossy` in ABP.agda.
C    : CProc                 -- cin?x → C' x
C'   : Bool → CProc          -- (cout!x → C' x) ⊓ (cin?y → C' y)   [inlined ⊓]
Cout : Bool → CProc          -- cout!x → C' x   (the output-resolved branch)
Cacc : Bool → CProc          -- cin?y → C' y    (the overwrite-resolved branch)

force C = react
  (λ where (_ , cin) x → just (C' x)
           (_ , cout) _ → nothing ; (_ , lose) _ → nothing ; (_ , dup) _ → nothing)
  ∅t
force (C' x) = react ∅v
  (λ where (_ , fin) (lift fzero)              → just (Cout x)
           (_ , fin) (lift (fsuc fzero))       → just (Cacc x)
           (_ , fin) (lift (fsuc (fsuc _)))    → nothing
           (_ , base _) _                      → nothing
           (_ , pair _ _) _                    → nothing)
force (Cout x) = react
  (λ where (_ , cout) y → case y B≟ x of λ where (yes _) → just (C' x) ; (no _) → nothing
           (_ , cin) _ → nothing ; (_ , lose) _ → nothing ; (_ , dup) _ → nothing)
  ∅t
force (Cacc x) = react
  (λ where (_ , cin) y → just (C' y)
           (_ , cout) _ → nothing ; (_ , lose) _ → nothing ; (_ , dup) _ → nothing)
  ∅t

------------------------------------------------------------------------------------
-- §5. Errors, CHAOSE and the LAZY ABSTRACTION operator LAbsE.
--   Errors = {lose,dup}
--   CHAOS(X) = STOP |~| ([] e:X -> CHAOS(X))
--   LAbs(X)(P) = (P [|X|] CHAOS(X)) \ X          -- normal(…) = identity, omitted
Errors : EventSet
Errors .mem (_ , lose) _ = ⊤poly {lzero} ; Errors .mem (_ , dup) _ = ⊤poly {lzero}
Errors .mem (_ , cin) _ = ⊥            ; Errors .mem (_ , cout) _ = ⊥
Errors .dec (_ , lose) _ = yes tt      ; Errors .dec (_ , dup) _ = yes tt
Errors .dec (_ , cin) _ = no (λ z → z) ; Errors .dec (_ , cout) _ = no (λ z → z)

-- CHAOSE is an internal choice (no visible offers, `react ∅v`) between STOP and
-- the "errors on" state `CHAOSon` (the same inlined-`⊓` shape as `C'`/`BElossy`).
CHAOSE  : CProc            -- STOP ⊓ (lose → CHAOSE □ dup → CHAOSE)
CHAOSon : CProc            -- lose → CHAOSE □ dup → CHAOSE

force CHAOSE = react ∅v
  (λ where (_ , fin) (lift fzero)              → just Stop
           (_ , fin) (lift (fsuc fzero))       → just CHAOSon
           (_ , fin) (lift (fsuc (fsuc _)))    → nothing
           (_ , base _) _                      → nothing
           (_ , pair _ _) _                    → nothing)
force CHAOSon = react
  (λ where (_ , lose) _ → just CHAOSE ; (_ , dup) _ → just CHAOSE
           (_ , cin) _ → nothing ; (_ , cout) _ → nothing)
  ∅t

LAbsE : CProc → CProc
LAbsE P = (Par⊤ Errors P CHAOSE) ∖ Errors

------------------------------------------------------------------------------------
-- §B. Errors-off reliability:  COPY ⊑FD (CE ⟦Errors⟧ Stop).
--
--   With {lose,dup} synchronised against `Stop` (which offers NEITHER), CE's error
--   arms are DEAD: a synchronised `lose`/`dup` needs BOTH operands to offer it, and
--   Stop offers nothing, so `par-pVis` yields `nothing` for every error event.  The
--   composite therefore reaches only the errors-off states
--       Par⊤ Errors CE Stop        (behaves as COPY, empty)
--       Par⊤ Errors (CEmid x) Stop (behaves as COPYout x: PINNED cout!x)
--       Par⊤ Errors (CE' x) Stop   (behaves as COPY again: dup blocked, cin?y only)
--   giving a 3-state correspondence with COPY / COPYout — identical visible offers,
--   all stable (both operands are `react … ∅t`, so the composite's τ-branch map
--   `par-pTau` is everywhere-`nothing`, hence τ-free and non-divergent).
--
--   ROUTE: the (recommended) BRIDGE route — a divergence-respecting weak bisimulation
--   `≈DR` built with `DRFromRel` (the two divergence obligations vacuous by
--   τ-freeness), then `drbisim→⊑FD`.  This INHERITS the one certified classical
--   postulate of the development, `¬-divergent→normal` (in `Semantics.DRImpliesFD`,
--   inside `drbisim→⊇F⊥`), exactly as the chapter 1–3 FD results and Buffers §B do.
--   §B itself adds no postulate / NON_TERMINATING / TERMINATING / mutual / Sized.
--
--   The `lose`/`dup` impossibility is discharged operationally: on the composite side
--   every error event forces `par-pVis … ≡ nothing` (Stop's `viewV` is `nothing`), so
--   the corresponding `bwdE` step-cases close with `case br of λ ()`.

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (trans; sym)

-- `Diverges` is hidden here because `Semantics.DRBisim` re-exports the very same LTS
-- `Diverges`; importing both unqualified would make the name ambiguous.
open import Semantics.LTS         {E = CEv} {I = ExtI CEv} hiding (Diverges)
open import Semantics.WeakBisim   {E = CEv} {I = ExtI CEv} using (_═[_]═►_; wev; τ*-refl)
open import Semantics.DRBisim     {E = CEv} {I = ExtI CEv} using (Diverges; _≈DR_)
open import Semantics.DRImpliesFD {E = CEv} {I = ExtI CEv} using (drbisim→⊑FD)
open import Semantics.FailuresDivergences {E = CEv} {I = ExtI CEv} using (_⊑FD_)
open import Semantics.BisimFromRel {E = CEv} {I = ExtI CEv}
-- the gathered stability layer: `stable-no-τ` (generic) + `Par-stable` (parallel intro)
open import Semantics.Stability {E = CEv} {I = ExtI CEv} using (stable-no-τ)
open import CSP.Laws.FD.ParallelRefusals CEv-≟ using (Par-stable)

-- The 3-state correspondence (COPY / COPYout ↔ the errors-off composite states).
data CRel : CProc → CProc → Set where
  rel-copy :         CRel COPY        (Par⊤ Errors CE Stop)
  rel-mid  : ∀ x → CRel (COPYout x) (Par⊤ Errors (CEmid x) Stop)
  rel-post : ∀ x → CRel COPY        (Par⊤ Errors (CE' x)  Stop)

-- COPY-side single visible steps (plain `react … ∅t` nodes; Buffers-style).
copy-in-fire : ∀ x → COPY ─[ ev (evl (evLabel Bool cin x)) ]─► COPYout x
copy-in-fire x = sVis {at = Bool , cin} {a = x} refl refl

copyout-fire : ∀ x {y} → y ≡ x → COPYout x ─[ ev (evl (evLabel Bool cout y)) ]─► COPY
copyout-fire x refl = go x
  where go : ∀ x → COPYout x ─[ ev (evl (evLabel Bool cout x)) ]─► COPY
        go true  = sVis {at = Bool , cout} {a = true}  refl refl
        go false = sVis {at = Bool , cout} {a = false} refl refl

-- Composite-side single visible steps.  `cin`/`cout` ∉ Errors ⇒ solo-L past the idle
-- Stop; the target `just (Par P' Stop)` is computed by `par-pVis`'s no-sync clause.
comp-in-CE : ∀ x → Par⊤ Errors CE Stop
                 ─[ ev (evl (evLabel Bool cin x)) ]─► Par⊤ Errors (CEmid x) Stop
comp-in-CE x = sVis {at = Bool , cin} {a = x} refl refl

comp-in-CE' : ∀ x y → Par⊤ Errors (CE' x) Stop
                    ─[ ev (evl (evLabel Bool cin y)) ]─► Par⊤ Errors (CEmid y) Stop
comp-in-CE' x y = sVis {at = Bool , cin} {a = y} refl refl

comp-out : ∀ x {y} → y ≡ x → Par⊤ Errors (CEmid x) Stop
                   ─[ ev (evl (evLabel Bool cout y)) ]─► Par⊤ Errors (CE' x) Stop
comp-out x refl = go x
  where go : ∀ x → Par⊤ Errors (CEmid x) Stop
                 ─[ ev (evl (evLabel Bool cout x)) ]─► Par⊤ Errors (CE' x) Stop
        go true  = sVis {at = Bool , cout} {a = true}  refl refl
        go false = sVis {at = Bool , cout} {a = false} refl refl

-- TAU-FREENESS of both sides of `CRel`.  Every operand here forces to `react … ∅t`,
-- so `isStable` reduces to the single clause `λ _ _ → refl`; `Par-stable` lifts that
-- through the parallel and `stable-no-τ` turns it into τ-freeness.  This replaces a
-- hand-rolled "`par-pTau` is everywhere `nothing`" index case split — the gathered
-- stability layer is `CSP.Laws.Stability.Closure`.

-- the ⊤-valued merge that `Par⊤` uses (spelled out so `Par-stable` can be applied)
mrg⊤ : ⊤poly {lzero} → ⊤poly {lzero} → ⊤poly {lzero}
mrg⊤ _ _ = tt

-- τ-freeness of the COPY side.
noτ-L : ∀ {p q} → CRel p q → ∀ {p′} → p ─[ τ ]─► p′ → ⊥
noτ-L rel-copy     = stable-no-τ {t = COPY}      (λ _ _ → refl)
noτ-L (rel-mid x)  = stable-no-τ {t = COPYout x} (λ _ _ → refl)
noτ-L (rel-post x) = stable-no-τ {t = COPY}      (λ _ _ → refl)

-- τ-freeness of the composite side (`Par-stable` on two stable operands).
noτ-R : ∀ {p q} → CRel p q → ∀ {q′} → q ─[ τ ]─► q′ → ⊥
noτ-R rel-copy     = stable-no-τ (Par-stable Errors mrg⊤ CE        Stop (λ _ _ → refl) (λ _ _ → refl))
noτ-R (rel-mid x)  = stable-no-τ (Par-stable Errors mrg⊤ (CEmid x) Stop (λ _ _ → refl) (λ _ _ → refl))
noτ-R (rel-post x) = stable-no-τ (Par-stable Errors mrg⊤ (CE' x)   Stop (λ _ _ → refl) (λ _ _ → refl))

-- The `DRFromRel` obligations.  Visible steps match on `cin`/`cout`; `lose`/`dup`
-- step-cases are impossible (Stop refuses ⇒ `par-pVis … ≡ nothing` ⇒ `case br of λ ()`).
fwdE : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′} → CRel p q → p ─[ ev l ]─► p′
     → Σ[ q′ ∈ CProc ] ((q ═[ ev l ]═► q′) × CRel p′ q′)
fwdE rel-copy (sRet ())
fwdE rel-copy (sVis {at = _ , cin}  {a = x} refl br) =
  case br of λ { refl → Par⊤ Errors (CEmid x) Stop , wev τ*-refl (comp-in-CE x) τ*-refl , rel-mid x }
fwdE rel-copy (sVis {at = _ , cout} refl br) = case br of λ ()
fwdE rel-copy (sVis {at = _ , lose} refl br) = case br of λ ()
fwdE rel-copy (sVis {at = _ , dup}  refl br) = case br of λ ()
fwdE (rel-mid x) (sRet ())
fwdE (rel-mid x) (sVis {at = _ , cin}  refl br) = case br of λ ()
fwdE (rel-mid x) (sVis {at = _ , cout} {a = y} refl br) with y B≟ x
... | yes e = case br of λ { refl → Par⊤ Errors (CE' x) Stop , wev τ*-refl (comp-out x e) τ*-refl , rel-post x }
... | no ¬p = case br of λ ()
fwdE (rel-mid x) (sVis {at = _ , lose} refl br) = case br of λ ()
fwdE (rel-mid x) (sVis {at = _ , dup}  refl br) = case br of λ ()
fwdE (rel-post x) (sRet ())
fwdE (rel-post x) (sVis {at = _ , cin}  {a = y} refl br) =
  case br of λ { refl → Par⊤ Errors (CEmid y) Stop , wev τ*-refl (comp-in-CE' x y) τ*-refl , rel-mid y }
fwdE (rel-post x) (sVis {at = _ , cout} refl br) = case br of λ ()
fwdE (rel-post x) (sVis {at = _ , lose} refl br) = case br of λ ()
fwdE (rel-post x) (sVis {at = _ , dup}  refl br) = case br of λ ()

bwdE : ∀ {p q} {l : Event√ (⊤poly {lzero})} {q′} → CRel p q → q ─[ ev l ]─► q′
     → Σ[ p′ ∈ CProc ] ((p ═[ ev l ]═► p′) × CRel p′ q′)
bwdE rel-copy (sRet ())
bwdE rel-copy (sVis {at = _ , cin}  {a = x} refl br) =
  case br of λ { refl → COPYout x , wev τ*-refl (copy-in-fire x) τ*-refl , rel-mid x }
bwdE rel-copy (sVis {at = _ , cout} refl br) = case br of λ ()
bwdE rel-copy (sVis {at = _ , lose} refl br) = case br of λ ()   -- lose ∈ Errors, Stop refuses ⇒ dead
bwdE rel-copy (sVis {at = _ , dup}  refl br) = case br of λ ()   -- dup  ∈ Errors, Stop refuses ⇒ dead
bwdE (rel-mid x) (sRet ())
bwdE (rel-mid x) (sVis {at = _ , cin}  refl br) = case br of λ ()
bwdE (rel-mid x) (sVis {at = _ , cout} {a = y} refl br) with y B≟ x
... | yes e = case br of λ { refl → COPY , wev τ*-refl (copyout-fire x e) τ*-refl , rel-post x }
... | no ¬p = case br of λ ()
bwdE (rel-mid x) (sVis {at = _ , lose} refl br) = case br of λ ()   -- CEmid offers lose, Stop refuses ⇒ dead
bwdE (rel-mid x) (sVis {at = _ , dup}  refl br) = case br of λ ()
bwdE (rel-post x) (sRet ())
bwdE (rel-post x) (sVis {at = _ , cin}  {a = y} refl br) =
  case br of λ { refl → COPYout y , wev τ*-refl (copy-in-fire y) τ*-refl , rel-mid y }
bwdE (rel-post x) (sVis {at = _ , cout} refl br) = case br of λ ()
bwdE (rel-post x) (sVis {at = _ , lose} refl br) = case br of λ ()
bwdE (rel-post x) (sVis {at = _ , dup}  refl br) = case br of λ ()   -- CE' offers dup, Stop refuses ⇒ dead

fwdT : ∀ {p q p′} → CRel p q → p ─[ τ ]─► p′
     → Σ[ q′ ∈ CProc ] ((q ═[ τ ]═► q′) × CRel p′ q′)
fwdT r pτ = ⊥-elim (noτ-L r pτ)

bwdT : ∀ {p q q′} → CRel p q → q ─[ τ ]─► q′
     → Σ[ p′ ∈ CProc ] ((p ═[ τ ]═► p′) × CRel p′ q′)
bwdT r qτ = ⊥-elim (noτ-R r qτ)

ndivL : ∀ {p q} → CRel p q → Diverges p → ⊥
ndivL r d = noτ-L r (d .Diverges.step)

ndivR : ∀ {p q} → CRel p q → Diverges q → ⊥
ndivR r d = noτ-R r (d .Diverges.step)

open DRFromRel CRel fwdE fwdT bwdE bwdT ndivL ndivR

copy≈DR-ce : COPY ≈DR (Par⊤ Errors CE Stop)
copy≈DR-ce = rel→dr rel-copy

-- Errors-off ⇒ reliable one-place buffer:  COPY [FD= CE ⟦Errors⟧ Stop.
copy-ce-reliable : COPY ⊑FD (Par⊤ Errors CE Stop)
copy-ce-reliable = drbisim→⊑FD copy≈DR-ce

------------------------------------------------------------------------------------
-- §C. Lazy abstraction of the error channel = the lossy/dup medium (STABLE FAILURES).
--
--   LAbsE CE = (Par⊤ Errors CE CHAOSE) ∖ Errors
--
-- Synchronising CE with CHAOSE on {lose,dup} and HIDING them: a fired lose/dup (with
-- CHAOSE resolved to its errors-ON branch CHAOSon) becomes an internal τ; CHAOSE's
-- STOP-branch supplies the refuse-option.  The composite is a 4×3 grid
--   (CE-state ∈ {CE, CEmid x, CE' x, CEdup x}) × (CHAOSE-state ∈ {CHAOSE, Stop, CHAOSon}).
-- CHAOSE is UNSTABLE (τ to Stop / CHAOSon); the hidden lose/dup syncs are further τ.
-- The STABLE hidden states and their visible offers:
--   (CE,Stop) (CE,CHAOSon) (CE' x,Stop)               : offer cin?y      (≈ C / Cacc x)
--   (CEmid x,Stop) (CEdup x,Stop) (CEdup x,CHAOSon)    : offer cout!x     (≈ Cout x)
-- which are exactly C's two stable refusal profiles — so, semantically, C ≈F LAbsE CE
-- (F ignores the abstraction's divergence — why the source uses [F=).
--
-- ⚠ ASSERT 2  (`c-eq-labs-ce : (C ⊑F LAbsE CE) × (LAbsE CE ⊑F C)`)  is DEFERRED.
-- What LANDED (below): the full LAbsE-CE step/τ CHARACTERISATION — the component single
-- steps and the composite (hidden) intro steps: the kept visible cin/cout (`soloL-keep`),
-- the CHAOSE-resolution τ (`labs-res-stop`/`labs-res-on`), and the hidden lose/dup syncs
-- turned into τ (`labs-lose`/`labs-dup`, via `sync-hide`).
-- Why the equivalence is deferred (after a genuine attempt): the correspondence is NOT a
-- forward weak simulation — C' x is a SINGLE nondeterministic state resolving to either
-- Cout x (offers cout!x) or Cacc x (offers cin), but NO reachable stable composite state
-- can, from one threaded run, match BOTH resolutions (once CHAOSE resolves to Stop the
-- medium is deterministic and cannot re-output; keeping CHAOSon the cin-offer is never
-- STABLE).  The equivalence therefore holds only at the FAILURES level (a UNION over
-- runs, choosing the composite run per (trace, endpoint) — no single simulation).  The
-- backward direction `C ⊑F LAbsE CE` further requires inverting arbitrary interleavings
-- of the hidden τ (res/lose/dup) with visible cin/cout across the 12-state Par∖ grid —
-- i.e. general Par-∖ de-interleaving AT THE FAILURES level, the unfinished machinery
-- flagged in `CSP.Laws.Traces.TraceLawsParallel` ("the big remaining piece").  Deferred
-- per the sanctioned fallback (cf. the plain-ABP refinement / general4 deadlock-free).

open import Data.Unit as DU using ()
open import CSP.Laws.Traces.TraceLawsHide CEv-≟
  using (Hide-keep; Hide-hidden; Hide-τ)
open import CSP.Laws.Traces.TraceLawsParallel CEv-≟
  using (Par-soloL; Par-sync; Par-τ-R)

-- §C.1 Component single steps (react nodes ⇒ hold by refl; PINNED outputs split Bool).
ce-in : ∀ x → CE ─[ ev (evl (evLabel Bool cin x)) ]─► CEmid x
ce-in x = sVis {at = Bool , cin} {a = x} refl refl

cemid-out : ∀ x → CEmid x ─[ ev (evl (evLabel Bool cout x)) ]─► CE' x
cemid-out true  = sVis {at = Bool , cout} {a = true}  refl refl
cemid-out false = sVis {at = Bool , cout} {a = false} refl refl

cemid-lose : ∀ x → CEmid x ─[ ev (evl (evLabel DU.⊤ lose DU.tt)) ]─► CE
cemid-lose x = sVis {at = DU.⊤ , lose} {a = DU.tt} refl refl

ce'-in : ∀ x y → CE' x ─[ ev (evl (evLabel Bool cin y)) ]─► CEmid y
ce'-in x y = sVis {at = Bool , cin} {a = y} refl refl

ce'-dup : ∀ x → CE' x ─[ ev (evl (evLabel DU.⊤ dup DU.tt)) ]─► CEdup x
ce'-dup x = sVis {at = DU.⊤ , dup} {a = DU.tt} refl refl

cedup-out : ∀ x → CEdup x ─[ ev (evl (evLabel Bool cout x)) ]─► CE' x
cedup-out true  = sVis {at = Bool , cout} {a = true}  refl refl
cedup-out false = sVis {at = Bool , cout} {a = false} refl refl

chaose-stop : CHAOSE ─[ τ ]─► Stop
chaose-stop = sTau {i = Lift lzero (Fin 2) , fin} {a = lift fzero} refl refl
chaose-on : CHAOSE ─[ τ ]─► CHAOSon
chaose-on = sTau {i = Lift lzero (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl
chaoson-lose : CHAOSon ─[ ev (evl (evLabel DU.⊤ lose DU.tt)) ]─► CHAOSE
chaoson-lose = sVis {at = DU.⊤ , lose} {a = DU.tt} refl refl
chaoson-dup : CHAOSon ─[ ev (evl (evLabel DU.⊤ dup DU.tt)) ]─► CHAOSE
chaoson-dup = sVis {at = DU.⊤ , dup} {a = DU.tt} refl refl

-- §C.2 Composite (hidden) intro steps.
-- CHAOSE-resolution τ (P-component idle, kept ABSTRACT — Par-τ-R does not force P).
labs-res-stop : ∀ (P : CProc)
              → (Par⊤ Errors P CHAOSE ∖ Errors) ─[ τ ]─► (Par⊤ Errors P Stop ∖ Errors)
labs-res-stop P = Hide-τ Errors (Par⊤ Errors P CHAOSE)
                    (Par-τ-R Errors (λ _ _ → tt) P CHAOSE chaose-stop)
labs-res-on : ∀ (P : CProc)
            → (Par⊤ Errors P CHAOSE ∖ Errors) ─[ τ ]─► (Par⊤ Errors P CHAOSon ∖ Errors)
labs-res-on P = Hide-τ Errors (Par⊤ Errors P CHAOSE)
                  (Par-τ-R Errors (λ _ _ → tt) P CHAOSE chaose-on)

-- A NON-error visible event of the CE-component, kept (solo-L past the idle ch).
soloL-keep : ∀ {B} {e : CEv B} {a : B} {P P' : CProc} (ch : CProc)
           → ¬ Errors .mem (B , e) a
           → P ─[ ev (evl (evLabel B e a)) ]─► P'
           → viewV (PTree.force ch) (B , e) a ≡ nothing
           → (Par⊤ Errors P ch ∖ Errors) ─[ ev (evl (evLabel B e a)) ]─► (Par⊤ Errors P' ch ∖ Errors)
soloL-keep {B} {e} {a} ch ¬er step nq =
  Hide-keep Errors (Par⊤ Errors _ ch) ¬er
    (Par-soloL Errors (λ _ _ → tt) _ ch ¬er step nq)

-- A synchronised ERROR event of CE ∥ CHAOSon, hidden ⇒ becomes an internal τ.
sync-hide : ∀ {B} {e : CEv B} {a : B} {P P' ch ch' : CProc}
          → Errors .mem (B , e) a
          → P ─[ ev (evl (evLabel B e a)) ]─► P'
          → ch ─[ ev (evl (evLabel B e a)) ]─► ch'
          → (Par⊤ Errors P ch ∖ Errors) ─[ τ ]─► (Par⊤ Errors P' ch' ∖ Errors)
sync-hide {B} {e} {a} er sp sq =
  Hide-hidden Errors (Par⊤ Errors _ _) er
    (Par-sync Errors (λ _ _ → tt) _ _ er sp sq)

-- The hidden lose / dup τ (require CHAOSon; both go via CHAOSE back to accept / re-output).
labs-lose : ∀ x → (Par⊤ Errors (CEmid x) CHAOSon ∖ Errors) ─[ τ ]─► (Par⊤ Errors CE CHAOSE ∖ Errors)
labs-lose x = sync-hide {DU.⊤} {lose} {DU.tt} tt (cemid-lose x) chaoson-lose
labs-dup : ∀ x → (Par⊤ Errors (CE' x) CHAOSon ∖ Errors) ─[ τ ]─► (Par⊤ Errors (CEdup x) CHAOSE ∖ Errors)
labs-dup x = sync-hide {DU.⊤} {dup} {DU.tt} tt (ce'-dup x) chaoson-dup
