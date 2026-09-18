{-# OPTIONS --guardedness #-}

-- UCS chapter 3: ncopy — the UNHIDDEN chain of COPY cells (ncopy.csp, Bill Roscoe;
-- source fdr-examples/ucs/chapter03/ncopy.csp).  Reduced N = 2, T = Bool, matching the
-- sibling `CSP.Examples.UCS.Ch5.NCopy`: two cells COPY(0),COPY(1) over c.0,c.1,c.2,
-- alphabetised-parallel over AC(r) = {|c.r, c.r+1|}, synchronising on the shared
-- internal channel c.1.  At N = 2 the source's internal-channel set
-- `{|c.r | r <- {1..N-1}|}` is just `{|c.1|}`.
--
-- WHY BOTH FILES EXIST — the two ways of dealing with the internal traffic:
--   * ch5's `ncopyh.csp` HIDES it: `CCH = CC ∖ {|c.1|}`, and the c.1 handoff becomes a
--     τ, so the chain is literally a 2-place buffer (`Spec =T CCH`, `Spec ≈FD CCH`).
--   * ch3's `ncopy.csp` (this file) hides NOTHING and RELAXES THE SPECIFICATION
--     instead: `Spec = B(N,<>) ||| RUN({|c.1|})`.  The interleaved `RUN` makes the
--     specification indifferent to the internal channel — it permits arbitrary c.1
--     traffic at any point — while `B(N,<>)` still pins the c.0/c.2 buffer behaviour.
--     That is the pedagogical content of the chapter: "don't care on internal
--     channels" is an alternative to abstraction by hiding, and it is a strictly
--     WEAKER obligation (the specification's alphabet now covers c.1 permissively,
--     so no c.1 behaviour of the implementation can ever violate it).
--
-- The two source asserts are proved here, BOTH TRUE:
--   §B  `chain-safe : Spec₃ ⊑T CC`        — `assert Spec [T= CC`
--   §C  `chain-df   : DeadlockFree CC`    — `assert CC :[deadlock free]`
-- Their truth values were re-derived, not taken on trust.  `Semantics.Failures` fixes
-- `P ⊑T Q = ∀ s → traces Q s → traces P s`, i.e. spec on the LEFT (FDR's `Spec [T= Impl`),
-- so §B must show every CC trace is a Spec₃ trace: CC's four reachable states each map
-- to the buffer state holding the same contents, and CC's ONLY non-buffer event (the
-- visible c.1 handoff) is absorbed by `RUN` with the buffer standing still — hence the
-- refinement.  `Semantics.Deadlock`'s `DeadlockFree` asks that no √-free-reachable state
-- be stuck; unhidden, every one of the four states offers a visible event (c.0, c.1 or
-- c.2), so `Semantics.DeadlockDR`'s `progress⇒deadlockFree` applies directly.
--
-- REUSE: the model is IMPORTED WHOLESALE from `CSP.Examples.UCS.Ch5.NCopy` — the event
-- type `NEv`, the cells `Cell`/`Cell′`, the alphabets `AC0`/`AC1`, the composed chain
-- `CC` (ch5 defines it UNHIDDEN and then hides it, so `CC` is exactly this chapter's
-- process), the buffer `Buf`, and the reachability machinery `Chain`/`Reach`/`inv0`/
-- `inv1`/`noτ0`/`noτ1`/`noComp√`.  Even the internal-channel set is ch5's `Hset`,
-- re-exposed as `Cset` — the same event set, hidden there, tolerated here.  New here:
-- the relaxed spec `SpecC`/`Spec₃`, its step lemmas, and the two proofs.
--
-- CLASSICAL FOOTPRINT: none.  Postulate-free, like `Ch5/NCopy.agda` (and unlike
-- `Ch5/NCopyL.agda`, which rides the sanctioned `Hide-fsim`/`αpar-fsim-df` seams): the
-- whole closure — `CSP.Operators`, `CSP.Laws.AlphaParallel`, `Semantics.WeakSim`,
-- `Semantics.BisimFromRel`, `Semantics.Deadlock`, `Semantics.DeadlockDR` — carries no
-- `postulate`.  No `NON_TERMINATING`/`TERMINATING`, no sized types, no old-style
-- `mutual`, no holes.

module CSP.Examples.UCS.Ch3.NCopyChain where

open import Level using () renaming (zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-- the whole ch5 model: event type, cells, alphabets, the UNHIDDEN chain `CC`, the
-- buffer `Buf`, and the per-cell step inversions behind its reachability argument.
open import CSP.Examples.UCS.Ch5.NCopy

open import CSP.Operators NEv-≟
open import Semantics.LTS       {E = NEv} {I = ExtI NEv}
open import Semantics.WeakBisim {E = NEv} {I = ExtI NEv}
  using (_═[_]═►_; wev; wτ; τ*-refl)
open import Semantics.Failures  {E = NEv} {I = ExtI NEv} using (_⊑T_)
open import Semantics.WeakSim   {E = NEv} {I = ExtI NEv} using (WSim; wsim→⊑T)
open import Semantics.BisimFromRel {E = NEv} {I = ExtI NEv} using (module WSimFromRel)
open import Semantics.Deadlock  {E = NEv} {I = ExtI NEv}
  using (DeadlockFree; _⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DeadlockDR {E = NEv} {I = ExtI NEv}
  using (Progress; progress⇒deadlockFree)
open import CSP.Laws.AlphaParallel NEv-≟
  using (vSync; vSoloL; vSoloR; αpar-vis-step-inv; αpar-τ-step-inv)

------------------------------------------------------------------------------------
-- §A. Model: the relaxed specification  Spec = B(N,<>) ||| RUN({|c.1|}).
------------------------------------------------------------------------------------

-- `{|c.1|}`: the internal channel set.  At N = 2 the source's `{|c.r | r <- {1..N-1}|}`
-- is the single channel c.1 — which is precisely ch5's `Hset`, the set it HIDES.
Cset : EventSet
Cset = Hset

-- `RUN({|c.1|})`: always offers every c.1 event and nothing else.
Run₁ : CC2Proc
Run₁ = Run′ Cset

-- Interleaving at the composed-pair return type.  The exported `_⦀_` is pinned to the
-- CSP return type `⊤`, whereas `CC` (imported from ch5, built with `_⟦_∥_⟧_`) returns
-- the PAIR `⊤poly × ⊤poly`; `_⊑T_` needs both sides at the SAME return type, so we
-- instantiate the generic `Par` at the empty synchronisation set `∅ES` — exactly what
-- `_⦀_` does — with a pair-preserving merge.  Neither operand ever terminates, so the
-- merge is never reached.
infixr 5 _⦀ᴾ_
_⦀ᴾ_ : CC2Proc → CC2Proc → CC2Proc
P ⦀ᴾ Q = Par ∅ES (λ u _ → u) P Q

-- `B(N,s) ||| RUN({|c.1|})`: the buffer holding `cs`, indifferent to c.1 traffic.
SpecC : List Bool → CC2Proc
SpecC cs = Buf cs ⦀ᴾ Run₁

-- `Spec = B(N,<>) ||| RUN({|c.1|})` — the source's relaxed specification.
Spec₃ : CC2Proc
Spec₃ = SpecC []

------------------------------------------------------------------------------------
-- §B. chain-safe :  Spec₃ ⊑T CC   (`assert Spec [T= CC`).
--
-- Unhidden, `CC` is a four-state τ-FREE machine (ch5's `Reach` shapes, with the same
-- `contents` reading; only the c.1 handoff differs, being visible here):
--   e     both cells ready         contents []
--   l x   cell0 holds x            contents (x ∷ [])
--   r y   cell1 holds y            contents (y ∷ [])
--   f x y both cells hold          contents (y ∷ x ∷ [])
--   e   --c.0?x-->  l x        l x --c.1!x--> r x      (a VISIBLE sync, not a τ)
--   r y --c.0?x-->  f x y      r y --c.2!y--> e        f x y --c.2!y--> l x
-- The matching `Spec₃` moves: c.0/c.2 are the buffer's (RUN refuses them), and c.1 is
-- RUN's (the buffer refuses it) — so the c.1 handoff is matched with the buffer's
-- contents UNCHANGED, which is what `contents (l x) ≡ contents (r x)` says.
------------------------------------------------------------------------------------

-- §B.1 `Spec₃` steps.  Both operands force to `react` and their offers are disjoint,
-- so the interleaving's routing reduces and every step holds by `refl` (the c.2 output
-- guard `y B≟ x₀` needs the Bool concrete, hence those splits).

-- c.0?x into the empty buffer (RUN refuses c.0 ⇒ solo-left).
sp-c0-empty : ∀ x → SpecC [] ─[ ev (evl (cL (fz , x))) ]─► SpecC (x ∷ [])
sp-c0-empty x = sVis {at = _ , c} {a = fz , x} refl refl

-- c.0?x into a one-item buffer.
sp-c0-one : ∀ y x → SpecC (y ∷ []) ─[ ev (evl (cL (fz , x))) ]─► SpecC (y ∷ x ∷ [])
sp-c0-one y x = sVis {at = _ , c} {a = fz , x} refl refl

-- c.2!y out of a one-item buffer.
sp-c2-one : ∀ y → SpecC (y ∷ []) ─[ ev (evl (cL (fs (fs fz) , y))) ]─► SpecC []
sp-c2-one true  = sVis {at = _ , c} {a = fs (fs fz) , true}  refl refl
sp-c2-one false = sVis {at = _ , c} {a = fs (fs fz) , false} refl refl

-- c.2!y out of a full buffer.
sp-c2-two : ∀ y x → SpecC (y ∷ x ∷ []) ─[ ev (evl (cL (fs (fs fz) , y))) ]─► SpecC (x ∷ [])
sp-c2-two true  x = sVis {at = _ , c} {a = fs (fs fz) , true}  refl refl
sp-c2-two false x = sVis {at = _ , c} {a = fs (fs fz) , false} refl refl

-- the "don't care" step: RUN absorbs ANY c.1 event in ANY buffer state, and the buffer
-- contents are preserved.  This is the whole point of the relaxed specification.
sp-c1 : ∀ cs x → SpecC cs ─[ ev (evl (cL (fs fz , x))) ]─► SpecC cs
sp-c1 []              x = sVis {at = _ , c} {a = fs fz , x} refl refl
sp-c1 (y ∷ [])        x = sVis {at = _ , c} {a = fs fz , x} refl refl
sp-c1 (y ∷ z ∷ cs)    x = sVis {at = _ , c} {a = fs fz , x} refl refl

-- §B.2 the weak-simulation relation: a reachable chain config against the relaxed
-- specification holding the same contents.  The per-cell states s0/s1 stay ABSTRACT
-- (so the composite's `.force` stays stuck and the α-parallel inversion can infer the
-- alphabets AC0/AC1); the `Reach` witness is split AFTER the inversion.
data RR₃ : CC2Proc → CC2Proc → Set₁ where
  rr₃ : ∀ s0 s1 cs → Reach s0 s1 cs → RR₃ (Chain s0 s1) (SpecC cs)

-- §B.3 forward matching of a visible move of `CC`.
fwdE₃ : ∀ {p q} {lb : Event√ (⊤poly {lzero} × ⊤poly {lzero})} {p′}
      → RR₃ p q → p ─[ ev lb ]─► p′
      → Σ[ q′ ∈ CC2Proc ] ((q ═[ ev lb ]═► q′) × RR₃ p′ q′)
-- neither cell terminates, so the composite has no √.
fwdE₃ (rr₃ s0 s1 cs rc) (sRet eqf) = ⊥-elim (noComp√ s0 s1 eqf)
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) with αpar-vis-step-inv feq br
-- SYNC : the only sync channel is c.1, enabled exactly at the `l` shape — and there it
-- is the visible handoff, matched by RUN with the buffer standing still.
...     | vSync pA pB p0s p1s with rc
...       | reach-e with inv0 rdy0 p0s
...         | t0-in x = case pB of λ ()
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSync pA pB p0s p1s | reach-l x
      with inv0 (hld0 x) p0s | inv1 rdy1 p1s
...         | t0-out x | t1-in y = _ , wev τ*-refl (sp-c1 (y ∷ []) y) τ*-refl
                                    , rr₃ rdy0 (hld1 y) (y ∷ []) (reach-r y)
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSync pA pB p0s p1s | reach-r y
      with inv0 rdy0 p0s
...         | t0-in x = case pB of λ ()
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSync pA pB p0s p1s | reach-f x y
      with inv0 (hld0 x) p0s | inv1 (hld1 y) p1s
...         | t0-out x | ()
-- SOLO-LEFT : c.0?x (cell 0 ready) — the buffer accepts it; c.1!x (cell 0 holding) is
-- in AC1, contradicting solo.
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSoloL pA ¬pB p0s with rc
...       | reach-e with inv0 rdy0 p0s
...         | t0-in x = _ , wev τ*-refl (sp-c0-empty x) τ*-refl
                          , rr₃ (hld0 x) rdy1 (x ∷ []) (reach-l x)
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSoloL pA ¬pB p0s | reach-l x
      with inv0 (hld0 x) p0s
...         | t0-out x = ⊥-elim (¬pB tt)
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSoloL pA ¬pB p0s | reach-r y
      with inv0 rdy0 p0s
...         | t0-in x = _ , wev τ*-refl (sp-c0-one y x) τ*-refl
                          , rr₃ (hld0 x) (hld1 y) (y ∷ x ∷ []) (reach-f x y)
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSoloL pA ¬pB p0s | reach-f x y
      with inv0 (hld0 x) p0s
...         | t0-out x = ⊥-elim (¬pB tt)
-- SOLO-RIGHT : c.2!y (cell 1 holding) — the buffer outputs it; c.1?y (cell 1 ready) is
-- in AC0, contradicting solo.
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSoloR ¬pA pB p1s with rc
...       | reach-e with inv1 rdy1 p1s
...         | t1-in y = ⊥-elim (¬pA tt)
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSoloR ¬pA pB p1s | reach-l x
      with inv1 rdy1 p1s
...         | t1-in y = ⊥-elim (¬pA tt)
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSoloR ¬pA pB p1s | reach-r y
      with inv1 (hld1 y) p1s
...         | t1-out y = _ , wev τ*-refl (sp-c2-one y) τ*-refl
                            , rr₃ rdy0 rdy1 [] reach-e
fwdE₃ (rr₃ s0 s1 cs rc) (sVis {at = _ , c} feq br) | vSoloR ¬pA pB p1s | reach-f x y
      with inv1 (hld1 y) p1s
...         | t1-out y = _ , wev τ*-refl (sp-c2-two y x) τ*-refl
                            , rr₃ (hld0 x) rdy1 (x ∷ []) (reach-l x)

-- §B.4 the unhidden chain has NO τ at all: both cells are stable, and the c.1 handoff
-- is a visible sync (this is exactly what hiding would have turned into a τ).
noτ₃ : ∀ {p q p′} → RR₃ p q → p ─[ τ ]─► p′ → ⊥
noτ₃ (rr₃ s0 s1 cs rc) stp with αpar-τ-step-inv stp
... | inj₁ (_ , t0τ , _) = noτ0 s0 t0τ
... | inj₂ (_ , t1τ , _) = noτ1 s1 t1τ

-- … so the τ obligation of the weak simulation is vacuous.
fwdT₃ : ∀ {p q p′} → RR₃ p q → p ─[ τ ]─► p′
      → Σ[ q′ ∈ CC2Proc ] ((q ═[ τ ]═► q′) × RR₃ p′ q′)
fwdT₃ rel stp = ⊥-elim (noτ₃ rel stp)

module M₃ = WSimFromRel RR₃ fwdE₃ fwdT₃

-- assert  Spec [T= CC : every trace of the unhidden chain — internal c.1 events and
-- all — is a trace of the relaxed specification.  Seed: CC = Chain rdy0 rdy1 and
-- Spec₃ = SpecC [] (both by `refl`).
chain-safe : Spec₃ ⊑T CC
chain-safe = wsim→⊑T (M₃.rel→wsim (rr₃ rdy0 rdy1 [] reach-e))

------------------------------------------------------------------------------------
-- §C. chain-df :  DeadlockFree CC   (`assert CC :[deadlock free]`).
--
-- `Semantics.Deadlock.DeadlockFree` asks that no √-free-reachable state be stuck.  All
-- four reachable states offer a visible event, so `Progress` holds and
-- `Semantics.DeadlockDR.progress⇒deadlockFree` closes it.  (`Progress` is the cheapest
-- route precisely because the chain is τ-free: there is no divergence to consider and
-- reachability is preserved by §B's `fwdE₃`.)
------------------------------------------------------------------------------------

-- §C.1 one enabled move per reachable config, built by the α-parallel intro lemmas.

-- e --c.0?x--> l x : c.0 ∈ AC0 ∖ AC1, so cell 0 acts solo.
cc-e-c0 : ∀ x → Chain rdy0 rdy1 ─[ ev (evl (cL (fz , x))) ]─► Chain (hld0 x) rdy1
cc-e-c0 x = αpar-soloL-step {A = AC0} {B = AC1} {at = _ , c} {a = fz , x}
              tt (λ ()) refl refl refl

-- l x --c.1!x--> r x : the handoff.  c.1 ∈ AC0 ∩ AC1, so it is a SYNC — and, unhidden,
-- a visible event (in ch5 the very same step is the hidden τ).
cc-l-c1 : ∀ x → Chain (hld0 x) rdy1 ─[ ev (evl (cL (fs fz , x))) ]─► Chain rdy0 (hld1 x)
cc-l-c1 true  = αpar-sync-step {A = AC0} {B = AC1} {at = _ , c} {a = fs fz , true}
                  tt tt refl refl refl refl
cc-l-c1 false = αpar-sync-step {A = AC0} {B = AC1} {at = _ , c} {a = fs fz , false}
                  tt tt refl refl refl refl

-- r y --c.2!y--> e : c.2 ∈ AC1 ∖ AC0, so cell 1 acts solo.
cc-r-c2 : ∀ y → Chain rdy0 (hld1 y) ─[ ev (evl (cL (fs (fs fz) , y))) ]─► Chain rdy0 rdy1
cc-r-c2 true  = αpar-soloR-step {A = AC0} {B = AC1} {at = _ , c} {a = fs (fs fz) , true}
                  (λ ()) tt refl refl refl
cc-r-c2 false = αpar-soloR-step {A = AC0} {B = AC1} {at = _ , c} {a = fs (fs fz) , false}
                  (λ ()) tt refl refl refl

-- f x y --c.2!y--> l x : same solo output, cell 0 still holding x.
cc-f-c2 : ∀ x y → Chain (hld0 x) (hld1 y)
                    ─[ ev (evl (cL (fs (fs fz) , y))) ]─► Chain (hld0 x) rdy1
cc-f-c2 x true  = αpar-soloR-step {A = AC0} {B = AC1} {at = _ , c} {a = fs (fs fz) , true}
                    (λ ()) tt refl refl refl
cc-f-c2 x false = αpar-soloR-step {A = AC0} {B = AC1} {at = _ , c} {a = fs (fs fz) , false}
                    (λ ()) tt refl refl refl

-- §C.2 every reachable config has an enabled label (`e` and `r`/`f` fire c.0 / c.2,
-- `l` fires the c.1 handoff), so none of them is stuck.
move₃ : ∀ {p q} → RR₃ p q
      → Σ[ l ∈ Label (⊤poly {lzero} × ⊤poly {lzero}) ] Σ[ p″ ∈ CC2Proc ] (p ─[ l ]─► p″)
move₃ (rr₃ s0 s1 cs rc) with rc
... | reach-e     = _ , _ , cc-e-c0 true
... | reach-l x   = _ , _ , cc-l-c1 x
... | reach-r y   = _ , _ , cc-r-c2 y
... | reach-f x y = _ , _ , cc-f-c2 x y

-- §C.3 `Progress` along a √-free run: `RR₃` is preserved by visible steps (§B's
-- `fwdE₃`) and no τ is ever available (§B's `noτ₃`), so the run stays in the four
-- reachable configs and `move₃` always applies.
prog₃ : ∀ {p q} → RR₃ p q → Progress p
prog₃ rel ∖√-refl         = move₃ rel
prog₃ rel (∖√-τ  st rest) = ⊥-elim (noτ₃ rel st)
prog₃ rel (∖√-ev st rest) with fwdE₃ rel st
... | _ , _ , rel′ = prog₃ rel′ rest

-- assert  CC :[deadlock free] : the unhidden COPY chain never gets stuck.
chain-df : DeadlockFree CC
chain-df = progress⇒deadlockFree (prog₃ (rr₃ rdy0 rdy1 [] reach-e))
