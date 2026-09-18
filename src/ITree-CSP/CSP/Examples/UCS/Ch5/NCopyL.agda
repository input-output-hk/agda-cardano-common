{-# OPTIONS --guardedness #-}

-- UCS chapter 5: ncopyl — chaining COPY processes with LINK PARALLEL (ncopyl.csp,
-- Bill Roscoe; source fdr-examples/ucs/chapter05/ncopyl.csp).  Reduced N = 2,
-- T = {0,1} = Bool (as in the sibling `CSP.Examples.UCS.Ch5.NCopy`, which ports the
-- indexed-channel variant ncopyh.csp).
--
--     COPY   = left?x -> right!x -> COPY
--     CCL(1) = COPY
--     CCL(n) = CCL(n-1)[left <-> right] COPY
--     B(s)   = #s<N & left?x -> B(s^<x>)  []  #s>0 & right.head(s) -> B(tail(s))
--     Spec   = B(<>)
--     assert Spec [T= CCL(N)   /   assert CCL(N) [T= Spec         (proved here)
--     assert Spec [FD= CCL(N)  /   assert CCL(N) [FD= Spec        (proved here, §C.3)
--
-- WHAT IS DIFFERENT FROM ncopyh / `Ch5.NCopy`.  ncopyh builds the chain out of two
-- DIFFERENTLY INDEXED cells `COPY(n) = c.n?x -> c.n+1!x -> COPY(n)`, composed with an
-- alphabetised parallel over an explicitly hidden internal channel.  ncopyl has ONE
-- unindexed `COPY` over `left`/`right`, and the link-parallel operator does the
-- channel matching AND the hiding.  So here BOTH operands of the chain are the SAME
-- process `COPY` (§A.2) — see `ccl-same-cell` (§A.5), which states that fact as a
-- definitional equality.
--
-- TRUTH VALUES (re-derived, not taken on trust).  `Semantics.Failures` fixes the
-- direction convention `P ⊑T Q = ∀ s → traces Q s → traces P s` (spec on the LEFT,
-- FDR's `Spec [T= Impl`), and `Semantics.FailuresDivergences` fixes `⊑F⊥`/`⊑D`/`⊑FD`
-- the same way.  All four asserts are TRUE: the two-cell chain and the two-place
-- buffer have the same traces (each refines the other), and — since the chain is
-- divergence-free and, after the internal handoff τ, offers exactly the buffer's
-- events — the same failures and divergences.  ALL FOUR are proved here: the two [T=
-- asserts in §C.2 and Roscoe's two chapter-6 [FD= ones in §C.3.
--
-- CONSTRUCTION — ROUTE CHOSEN, AND WHAT WAS REJECTED.
-- Link parallel is not an operator of this development.  It is derivable:
-- `P [x <-> y] Q` relabels P's `x` and Q's `y` onto a common channel, alphabetised-
-- parallels them on it, and hides it.  Two routes were on the table:
--   (a) a derived link-parallel combinator;
--   (b) instantiate the event type so the link channel is already present and apply
--       `renameInv`/`renameMap` to the single `COPY` at composition time.
-- We take BOTH, in the cheapest honest combination: (b) supplies the event type —
-- we REUSE the sibling's `NEv` (`c : NEv (Fin 3 × Bool)`, so c.0/c.1/c.2 are three
-- channels) — and (a) wraps the resulting relabel-parallel-hide sandwich in one
-- LOCAL combinator `_[l↔r]_` (§A.4).  The combinator is deliberately local: no
-- shared module (`CSP.Operators`, `CSP.Rename`, `Semantics.*`, `CSP.Laws.*`) is
-- touched.
--
-- The one design choice worth spelling out is WHICH channel is the link.  The
-- textbook derivation invents a FRESH channel `m` and renames BOTH operands
-- (P's `left` and Q's `right`) onto it.  We instead let the link BE the right-hand
-- operand's own `right` (c.1) and shift the left-hand operand's alphabet up by one
-- channel (`left`↦c.1, `right`↦c.2, the `shift` relabelling of §A.3).  That is the
-- same construction composed with an injective relabelling of the composite's
-- external interface — the composite's external channels are c.0 (the upstream
-- COPY's `left`) and c.2 (the downstream COPY's `right`, i.e. B's `right`) — so the
-- asserts are the image of Roscoe's under an injective renaming of the whole system
-- and hold iff his do.  It buys two things: the UPSTREAM operand needs no rename at
-- all (it is literally `COPY`), and the renamed downstream operand lines up with the
-- sibling's indexed cell, so the whole chain is `Ch5.NCopy`'s `CC` up to the
-- component simulation of §B — which is what lets us discharge the asserts by
-- REUSING `ncopy-safe` / `ncopy-live` rather than re-running their weak-simulation
-- proofs against a rename-wrapped cell.
--
-- REJECTED: (i) two differently indexed cells — that is ncopyh, i.e. the sibling
-- module, and would not port ncopyl at all; (ii) renaming both operands onto a
-- fresh fourth channel — correct but strictly more work (two component simulations
-- and two extra divergence-freedom certificates) for no extra content; (iii) redoing
-- `Ch5.NCopy`'s §B/§C weak simulations directly against the rename-wrapped chain —
-- postulate-free but ~400 lines of near-duplicate `with`-chains.
--
-- PROOF SHAPE (§B, §C).  The renamed `COPY` and the sibling's shifted cell are
-- failure-simulation equivalent (§B: one relation `RA`, two `FSimFromRel`
-- instantiations, using the generic rename step lemmas of
-- `CSP.Laws.Traces.RenameDeadlock`).  The equivalence is then transported through
-- the alphabetised parallel and the hide by `αpar-fsim-df` and `Hide-fsim` (§C),
-- giving `CCL =T CCH`, and composed with the sibling's two trace refinements.
--
-- CLASSICAL FOOTPRINT.  All FOUR of `Ch5.NCopy`'s theorems — the two trace ones and
-- the two FD ones it now supplies (`ncopy-safe-FD`/`ncopy-live-FD`) — are
-- postulate-free.  Every result HERE, trace and FD alike, rides the same transport
-- step through the FSim congruences, whose modules carry the repo's sanctioned
-- LEM-derivable seams (`CSP.Laws.FD.FDTransfer.Diverges-LEM` via `FSim.HideCong`, and
-- the divergence machinery behind `FSim.AlphaParCong`).  So the FD asserts add NO new
-- seam: they have exactly the classical footprint the [T= ones already had.  This
-- module itself contains no `postulate`, no `NON_TERMINATING`/`TERMINATING`, no sized
-- types and no holes.
--
-- The FD asserts cost two lines (§C.3).  §C's two `FSim`s already give `CCL ≈FD CCH`
-- (a failure simulation yields `⊑FD` by `fsim→⊑FD`, one projection further into the
-- same record than `fsim→⊑T`), so the asserts reduce to `Spec ≈FD CCH`, which the
-- sibling `Ch5.NCopy` §D now proves; each direction is then one `⊑FD-trans`.

module CSP.Examples.UCS.Ch5.NCopyL where

open import Level using (lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-- the sibling ncopyh port supplies the event type, the parameterised COPY cell, the
-- alphabets, the buffer specification and the two trace refinements of ITS chain
open import CSP.Examples.UCS.Ch5.NCopy
  using ( NEv; NEv-≟; SProc; CC2Proc; Cell; Cell′; AC0; AC1; Hset; CC; CCH; Spec; cL
        ; St0; rdy0; hld0; nd0; T0; t0-in; t0-out; inv0; noτ0; noRet0
        ; St1; rdy1; hld1; nd1; T1; t1-in; t1-out; inv1; noτ1; noRet1
        ; ncopy-safe; ncopy-live; ncopy-safe-FD; ncopy-live-FD )
open NEv

open import CSP.Operators NEv-≟

-- the same-alphabet injective renaming instance (identity event injection), exactly
-- as `Ch5.Renaming`: the relabelling happens at the VALUE level (the channel index
-- lives in `c`'s carried value), so it is supplied as an `inv` preimage map below
open import CSP.Rename {E₁ = NEv} {E₂ = NEv} (λ e → e) (λ e → just e) (λ _ → refl)
  using (ConcEvent₁; renameInv)

open import Semantics.LTS       {E = NEv} {I = ExtI NEv}
open import Semantics.WeakBisim {E = NEv} {I = ExtI NEv}
  using (_═[_]═►_; wev; _─[τ*]─►_; τ*-refl)
open import Semantics.Failures  {E = NEv} {I = ExtI NEv} using (_⊑T_; ⊑T-trans)
open import Semantics.Refusals  {E = NEv} {I = ExtI NEv} using (Offers)
open import Semantics.Stability {E = NEv} {I = ExtI NEv}
  using (stable-no-τ; stable→¬div; react-no-τ→stable)
open import Semantics.DivergenceFree {E = NEv} {I = ExtI NEv}
  using (τ-Acc; τ-AccReach; stable→τ-Acc)
open import Semantics.Deadlock  {E = NEv} {I = ExtI NEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.FailureSim {E = NEv} {I = ExtI NEv}
  using (FSim; fsim-refl; fsim→⊑T; fsim→⊑FD)
open import Semantics.FailuresDivergences {E = NEv} {I = ExtI NEv}
  using (_⊑FD_; _≈FD_; ⊑FD-trans)
open import Semantics.BisimFromRel {E = NEv} {I = ExtI NEv} using (module FSimFromRel)

open import CSP.Laws.Traces.RenameDeadlock {E₁ = NEv} {E₂ = NEv}
  (λ e → e) (λ e → just e) (λ _ → refl)
  using (ren-ev-inv; ren-τ-inv; ren-ev-fwd)
open import CSP.Laws.FSim.AlphaParCong NEv-≟ using (αpar-fsim-df)
open import CSP.Laws.FSim.HideCong     NEv-≟ using (Hide-fsim)

------------------------------------------------------------------------------------
-- §A. Model.
------------------------------------------------------------------------------------

-- §A.1 the three channels of the composite.  `left`/`right` are COPY's own two
-- channels; `right` doubles as the LINK channel (it is the one that gets hidden), and
-- `rightʹ` is where the downstream copy's `right` is shifted to — the composite's
-- external output, i.e. `right` as seen by the specification B.
left right rightʹ : Fin 3
left   = fz
right  = fs fz
rightʹ = fs (fs fz)

-- §A.2 COPY = left?x -> right!x -> COPY.  This is the sibling's parameterised cell
-- instantiated at (left, right) — the SAME definition, hence definitionally equal to
-- `nd0 rdy0`, which is what lets §B reuse the sibling's step inversions.
COPY : SProc
COPY = Cell left right

-- COPY holding x: right!x -> COPY
COPYh : Bool → SProc
COPYh x = Cell′ left right x

-- §A.3 the link relabelling used by `_[l↔r]_` on its LEFT (downstream) operand: a
-- target→source preimage map shifting the alphabet up one channel.  Target c.1 (the
-- link) comes from the source's `left`, target c.2 from the source's `right`; target
-- c.0 has no source (the shifted copy no longer uses the composite's input channel).
shift : (bt : AnyTypes NEv) → proj₁ bt → Maybe ConcEvent₁
shift (_ , c) (fz , _)         = nothing
shift (_ , c) (fs fz , x)      = just ((_ , c) , (left  , x))
shift (_ , c) (fs (fs fz) , x) = just ((_ , c) , (right , x))

-- §A.4 LINK PARALLEL (derived, local).  `P [l↔r] Q` is Roscoe's `P [left <-> right] Q`
-- at this instance: P (the downstream operand, whose `left` is linked) is shifted by
-- `shift`, Q (the upstream operand, whose `right` IS the link channel c.1) is left
-- alone, the two are alphabetised-parallelled — AC0 = {c.0,c.1} is Q's alphabet,
-- AC1 = {c.1,c.2} the shifted P's, so they synchronise exactly on the link — and the
-- link is hidden by Hset = {c.1}.  Operand order follows FDR's syntax; the operands
-- are handed to `_⟦_∥_⟧_` upstream-first so the composite is the sibling's `CC` shape.
_[l↔r]_ : SProc → SProc → CC2Proc
P [l↔r] Q = (Q ⟦ AC0 ∥ AC1 ⟧ renameInv P shift) ∖ Hset

-- §A.5 CCL(2) = COPY [left <-> right] COPY.  Both operands are the SAME `COPY`.
CCL : CC2Proc
CCL = COPY [l↔r] COPY

-- … and that is not a coincidence of notation: the chain really is built from one
-- process applied twice (the equation holds by `refl`).
ccl-same-cell : CCL ≡ ((COPY ⟦ AC0 ∥ AC1 ⟧ renameInv COPY shift) ∖ Hset)
ccl-same-cell = refl

------------------------------------------------------------------------------------
-- §B. The component simulation:  renameInv COPY shift  ≡  the sibling's shifted cell.
--
-- `renameInv COPY shift` offers c.1?x (from COPY's left?x) and then c.2!x (from
-- COPY's right!x): exactly the behaviour of `nd1 rdy1 = Cell right rightʹ`.  The two
-- are not definitionally equal (the renamed side carries a `renameInv` wrapper at
-- every state), so we relate them by a failure simulation in both directions.
------------------------------------------------------------------------------------

-- §B.1 stability of the two sides.  Both cells and their renames are `react` nodes
-- with an everywhere-`nothing` τ-map, so no state ever performs a τ.

-- the renamed COPY performs no τ: a renamed τ inverts to a τ of the operand
renNoτ : ∀ s0 {t′} → renameInv (nd0 s0) shift ─[ τ ]─► t′ → ⊥
renNoτ s0 stp with ren-τ-inv {inv = shift} {P = nd0 s0} stp
... | _ , pτ , _ = noτ0 s0 pτ

-- … hence it is stable (its force is a `react`, by the rename force-equation)
renStable : ∀ s0 → isStable (renameInv (nd0 s0) shift)
renStable rdy0     = react-no-τ→stable refl (renNoτ rdy0)
renStable (hld0 x) = react-no-τ→stable refl (renNoτ (hld0 x))

-- the sibling's upstream cell is stable
copyStable : ∀ s0 → isStable (nd0 s0)
copyStable rdy0     = react-no-τ→stable refl (noτ0 rdy0)
copyStable (hld0 x) = react-no-τ→stable refl (noτ0 (hld0 x))

-- … and so is its shifted cell
cellStable : ∀ s1 → isStable (nd1 s1)
cellStable rdy1     = react-no-τ→stable refl (noτ1 rdy1)
cellStable (hld1 x) = react-no-τ→stable refl (noτ1 (hld1 x))

-- §B.2 forward steps of the shifted cell (the value pin on the output needs the Bool
-- concrete, hence the split — cf. the sibling's `buf-c2-one`).

-- the cell accepts on the link channel: c.1?x
cellIn : ∀ x → nd1 rdy1 ─[ ev (evl (cL (right , x))) ]─► nd1 (hld1 x)
cellIn x = sVis {at = _ , c} {a = fs fz , x} refl refl

-- the cell emits its held value on the composite's output: c.2!x
cellOut : ∀ x → nd1 (hld1 x) ─[ ev (evl (cL (rightʹ , x))) ]─► nd1 rdy1
cellOut true  = sVis {at = _ , c} {a = fs (fs fz) , true}  refl refl
cellOut false = sVis {at = _ , c} {a = fs (fs fz) , false} refl refl

-- §B.3 the matching forward steps of the renamed COPY, pushed through the rename by
-- `ren-ev-fwd` (source step + the `shift` preimage equation).

-- the renamed COPY accepts on the link channel: c.1?x  (from COPY's left?x)
renIn : ∀ x → renameInv (nd0 rdy0) shift
              ─[ ev (evl (cL (right , x))) ]─► renameInv (nd0 (hld0 x)) shift
renIn x = ren-ev-fwd {inv = shift} {P = nd0 rdy0}
            {at = _ , c} {a = left , x} {bt = _ , c} {b = right , x}
            (sVis {at = _ , c} {a = fz , x} refl refl) refl

-- the renamed COPY emits on c.2  (from COPY's right!x)
renOut : ∀ x → renameInv (nd0 (hld0 x)) shift
               ─[ ev (evl (cL (rightʹ , x))) ]─► renameInv (nd0 rdy0) shift
renOut true  = ren-ev-fwd {inv = shift} {P = nd0 (hld0 true)}
                 {at = _ , c} {a = right , true} {bt = _ , c} {b = rightʹ , true}
                 (sVis {at = _ , c} {a = fs fz , true} refl refl) refl
renOut false = ren-ev-fwd {inv = shift} {P = nd0 (hld0 false)}
                 {at = _ , c} {a = right , false} {bt = _ , c} {b = rightʹ , false}
                 (sVis {at = _ , c} {a = fs fz , false} refl refl) refl

-- §B.4 the component relation: the renamed COPY's two states against the shifted
-- cell's two states.
data RA : SProc → SProc → Set₁ where
  ra-r :       RA (renameInv (nd0 rdy0) shift)     (nd1 rdy1)
  ra-h : ∀ x → RA (renameInv (nd0 (hld0 x)) shift) (nd1 (hld1 x))

-- §B.5 a visible step of the renamed COPY is matched by the cell at the SAME label.
-- `ren-ev-inv` reduces it to a step of `COPY` relabelled by `shift`; the sibling's
-- `inv0` then says which of COPY's two transitions fired (and refutes the rest).
renA→cell : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′}
          → RA p q → p ─[ ev l ]─► p′
          → Σ[ q′ ∈ SProc ] ((q ─[ ev l ]─► q′) × RA p′ q′)
-- COPY ready: only the link channel c.1 fires (c.0 has no source; c.2 would need
-- COPY to offer `right`, which it does not).
renA→cell ra-r stp with ren-ev-inv {inv = shift} {P = nd0 rdy0} stp
... | inj₂ (_ , _ , eqret , _) = ⊥-elim (noRet0 rdy0 eqret)
... | inj₁ (_ , _ , (_ , c) , (fz , _) , _ , _ , eqinv , _ , _) = case eqinv of λ ()
... | inj₁ (_ , _ , (_ , c) , (fs fz , x) , _ , Pev , refl , refl , refl)
      with inv0 rdy0 Pev
...     | t0-in _ = _ , cellIn x , ra-h x
renA→cell ra-r stp | inj₁ (_ , _ , (_ , c) , (fs (fs fz) , x) , _ , Pev , refl , refl , refl) =
  case inv0 rdy0 Pev of λ ()
-- COPY holding x: only c.2 fires (c.1 would need COPY to offer `left`).
renA→cell (ra-h x) stp with ren-ev-inv {inv = shift} {P = nd0 (hld0 x)} stp
... | inj₂ (_ , _ , eqret , _) = ⊥-elim (noRet0 (hld0 x) eqret)
... | inj₁ (_ , _ , (_ , c) , (fz , _) , _ , _ , eqinv , _ , _) = case eqinv of λ ()
... | inj₁ (_ , _ , (_ , c) , (fs fz , _) , _ , Pev , refl , refl , refl) =
        case inv0 (hld0 x) Pev of λ ()
... | inj₁ (_ , _ , (_ , c) , (fs (fs fz) , _) , _ , Pev , refl , refl , refl)
      with inv0 (hld0 x) Pev
...     | t0-out _ = _ , cellOut x , ra-r

-- §B.6 … and conversely: every visible step of the cell is matched by the renamed
-- COPY at the same label (`inv1` inverts the cell step; §B.3 rebuilds it renamed).
cell→renA : ∀ {p q} {l : Event√ (⊤poly {lzero})} {q′}
          → RA p q → q ─[ ev l ]─► q′
          → Σ[ p′ ∈ SProc ] ((p ─[ ev l ]─► p′) × RA p′ q′)
cell→renA ra-r (sRet eqf) = ⊥-elim (noRet1 rdy1 eqf)
cell→renA ra-r (sVis {at = at} {a = a} feq br)
  with inv1 rdy1 (sVis {at = at} {a = a} feq br)
... | t1-in x = _ , renIn x , ra-h x
cell→renA (ra-h x) (sRet eqf) = ⊥-elim (noRet1 (hld1 x) eqf)
cell→renA (ra-h x) (sVis {at = at} {a = a} feq br)
  with inv1 (hld1 x) (sVis {at = at} {a = a} feq br)
... | t1-out _ = _ , renOut x , ra-r

-- §B.7 the two `FSimFromRel` obligation bundles.  Neither side ever performs a τ, so
-- the τ-obligations are refutations and `stab` settles with an empty τ*-run.

-- a visible step is matched by a (trivially) weak step
fwdEA : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′}
      → RA p q → p ─[ ev l ]─► p′
      → Σ[ q′ ∈ SProc ] ((q ═[ ev l ]═► q′) × RA p′ q′)
fwdEA r stp with renA→cell r stp
... | q′ , s , r′ = q′ , wev τ*-refl s τ*-refl , r′

fwdEB : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′}
      → RA q p → p ─[ ev l ]─► p′
      → Σ[ q′ ∈ SProc ] ((q ═[ ev l ]═► q′) × RA q′ p′)
fwdEB r stp with cell→renA r stp
... | q′ , s , r′ = q′ , wev τ*-refl s τ*-refl , r′

-- the renamed COPY has no τ …
fwdTA : ∀ {p q p′} → RA p q → p ─[ τ ]─► p′
      → Σ[ q′ ∈ SProc ] ((q ═[ τ ]═► q′) × RA p′ q′)
fwdTA ra-r     stp = ⊥-elim (renNoτ rdy0 stp)
fwdTA (ra-h x) stp = ⊥-elim (renNoτ (hld0 x) stp)

-- … and neither has the cell
fwdTB : ∀ {p q p′} → RA q p → p ─[ τ ]─► p′
      → Σ[ q′ ∈ SProc ] ((q ═[ τ ]═► q′) × RA q′ p′)
fwdTB ra-r     stp = ⊥-elim (noτ1 rdy1 stp)
fwdTB (ra-h x) stp = ⊥-elim (noτ1 (hld1 x) stp)

-- offer transfer, cell → renamed (used by the renamed side's `stab`)
offA : ∀ {p q} → RA p q → ∀ (e : Event√ (⊤poly {lzero})) → Offers q e → Offers p e
offA r e (_ , s) with cell→renA r s
... | p′ , s′ , _ = p′ , s′

-- offer transfer, renamed → cell (used by the cell side's `stab`)
offB : ∀ {p q} → RA q p → ∀ (e : Event√ (⊤poly {lzero})) → Offers q e → Offers p e
offB r e (_ , s) with renA→cell r s
... | p′ , s′ , _ = p′ , s′

-- the spec side is already stable, so `stab` needs no τ*-settling
stabA : ∀ {p q} → RA p q → isStable p
      → Σ[ q′ ∈ SProc ] ((q ─[τ*]─► q′) × isStable q′
                        × (∀ (e : Event√ (⊤poly {lzero})) → Offers q′ e → Offers p e))
stabA ra-r     _ = _ , τ*-refl , cellStable rdy1     , offA ra-r
stabA (ra-h x) _ = _ , τ*-refl , cellStable (hld1 x) , offA (ra-h x)

stabB : ∀ {p q} → RA q p → isStable p
      → Σ[ q′ ∈ SProc ] ((q ─[τ*]─► q′) × isStable q′
                        × (∀ (e : Event√ (⊤poly {lzero})) → Offers q′ e → Offers p e))
stabB ra-r     _ = _ , τ*-refl , renStable rdy0     , offB ra-r
stabB (ra-h x) _ = _ , τ*-refl , renStable (hld0 x) , offB (ra-h x)

-- a stable implementation cannot diverge
ndivA : ∀ {p q} → RA p q → Diverges p → ⊥
ndivA ra-r     d = stable→¬div (renStable rdy0)     d
ndivA (ra-h x) d = stable→¬div (renStable (hld0 x)) d

ndivB : ∀ {p q} → RA q p → Diverges p → ⊥
ndivB ra-r     d = stable→¬div (cellStable rdy1)     d
ndivB (ra-h x) d = stable→¬div (cellStable (hld1 x)) d

-- the two component failure simulations (impl = renamed COPY / impl = cell)
module MA = FSimFromRel RA               fwdEA fwdTA stabA ndivA
module MB = FSimFromRel (λ p q → RA q p) fwdEB fwdTB stabB ndivB

------------------------------------------------------------------------------------
-- §C. Divergence-freedom of the operands, and the assembly.
--
-- `αpar-fsim-df` transports an `FSim` through the alphabetised parallel provided the
-- two SPEC operands are divergence-free at every √-free-reachable state (`τ-AccReach`).
-- Every operand here is a two-state stable machine, so reachability never leaves the
-- two states and each of them is τ-accessible vacuously.
------------------------------------------------------------------------------------

-- the upstream COPY: reachability stays inside {ready, holding x}
copyAR : ∀ s0 → τ-AccReach (nd0 s0)
copyAR s0 ∖√-refl          = stable→τ-Acc (copyStable s0)
copyAR s0 (∖√-τ stp _)     = ⊥-elim (noτ0 s0 stp)
copyAR s0 (∖√-ev stp rest) with inv0 s0 stp
copyAR rdy0     (∖√-ev stp rest) | t0-in x  = copyAR (hld0 x) rest
copyAR (hld0 x) (∖√-ev stp rest) | t0-out _ = copyAR rdy0 rest

-- the sibling's shifted cell: likewise
cellAR : ∀ s1 → τ-AccReach (nd1 s1)
cellAR s1 ∖√-refl          = stable→τ-Acc (cellStable s1)
cellAR s1 (∖√-τ stp _)     = ⊥-elim (noτ1 s1 stp)
cellAR s1 (∖√-ev stp rest) with inv1 s1 stp
cellAR rdy1     (∖√-ev stp rest) | t1-in x  = cellAR (hld1 x) rest
cellAR (hld1 x) (∖√-ev stp rest) | t1-out _ = cellAR rdy1 rest

-- the renamed COPY: a renamed run inverts to a run of COPY, so the same two states
renAR : ∀ s0 → τ-AccReach (renameInv (nd0 s0) shift)
renAR s0 ∖√-refl      = stable→τ-Acc (renStable s0)
renAR s0 (∖√-τ stp _) = ⊥-elim (renNoτ s0 stp)
renAR s0 (∖√-ev stp rest) with ren-ev-inv {inv = shift} {P = nd0 s0} stp
... | inj₂ (_ , _ , eqret , _) = ⊥-elim (noRet0 s0 eqret)
... | inj₁ (_ , _ , _ , _ , _ , Pev , _ , _ , refl) with inv0 s0 Pev
renAR rdy0     (∖√-ev stp rest) | inj₁ _ | t0-in x  = renAR (hld0 x) rest
renAR (hld0 x) (∖√-ev stp rest) | inj₁ _ | t0-out _ = renAR rdy0 rest

-- §C.1 the chains are failure-simulation equivalent: the left (upstream) operand is
-- the SAME `COPY` on both sides (`fsim-refl`), the right operand is §B's component
-- simulation, and the composite is transported through `⟦_∥_⟧` and `∖`.
fsimL : FSim (⊤poly {lzero} × ⊤poly {lzero}) CCL CCH
fsimL = Hide-fsim Hset
          (αpar-fsim-df AC0 AC1 (copyAR rdy0) (cellAR rdy1)
             (fsim-refl COPY) (MA.rel→fsim ra-r))

fsimR : FSim (⊤poly {lzero} × ⊤poly {lzero}) CCH CCL
fsimR = Hide-fsim Hset
          (αpar-fsim-df AC0 AC1 (copyAR rdy0) (renAR rdy0)
             (fsim-refl COPY) (MB.rel→fsim ra-r))

-- §C.2 the four-way conclusion.

-- assert Spec [T= CCL(2):  every trace of the link-parallel chain is a buffer trace.
ncopyl-safe : Spec ⊑T CCL
ncopyl-safe = ⊑T-trans ncopy-safe (fsim→⊑T fsimL)

-- assert CCL(2) [T= Spec:  the chain realises every 2-place-buffer trace.
ncopyl-live : CCL ⊑T Spec
ncopyl-live = ⊑T-trans (fsim→⊑T fsimR) ncopy-live

-- Combined:  Spec =T CCL(2).
ncopyl-≡T : (Spec ⊑T CCL) × (CCL ⊑T Spec)
ncopyl-≡T = ncopyl-safe , ncopyl-live

-- §C.3 the two chapter-6 asserts, transported through the SAME two `FSim`s.  A
-- failure simulation gives `⊑FD` as readily as `⊑T` (`fsim→⊑FD`, one projection
-- further into the same record), so once the sibling supplies `Spec ≈FD CCH` these
-- cost one `⊑FD-trans` each — no new relation, no new divergence certificate.

-- assert Spec [FD= CCL(2):  the link-parallel chain is a 2-place buffer in the FD model.
ncopyl-safe-FD : Spec ⊑FD CCL
ncopyl-safe-FD = ⊑FD-trans ncopy-safe-FD (fsim→⊑FD fsimL)

-- assert CCL(2) [FD= Spec:  and every buffer failure/divergence is the chain's.
ncopyl-live-FD : CCL ⊑FD Spec
ncopyl-live-FD = ⊑FD-trans (fsim→⊑FD fsimR) ncopy-live-FD

-- Combined:  Spec ≈FD CCL(2).
ncopyl-≈FD : Spec ≈FD CCL
ncopyl-≈FD = ncopyl-safe-FD , ncopyl-live-FD
