{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- NEGATIVE RESULT: `FinBr` is NOT a usable side condition for hide
-- monotonicity.  A conjectured
--
--     Hide-mono-⊑FD-finBr : FinBr P → P ⊑FD Q → (P ∖ A) ⊑FD (Q ∖ A)
--
-- is FALSE, because `FinBr` does not exclude the very counterexample that
-- refutes the unconditional law.
--
-- BACKGROUND.  `CSP.Laws.FD.HideMonoFD`'s header shows the unconditional law
-- fails on
--
--     Q = μX. h → X          (implementation: performs `h` for ever)
--     P = ⊓ₙ (hⁿ ; STOP)     (specification: infinitely-branching internal choice)
--
-- with `P ⊑FD Q` but `(P ∖ {h}) ⊑FD (Q ∖ {h})` false: `Q ∖ {h}` diverges while
-- `P ∖ {h}` cannot, since recovering an INFINITE hidden chain from arbitrarily
-- long finite ones is a König step, and König's lemma needs FINITE BRANCHING.
-- The natural repair is to demand a finite-branching certificate on the spec
-- side `P` — and `FinBr` (`Semantics.FinBr`) is the repo's only such certificate.
--
-- WHY IT DOES NOT WORK.  `FinBr` bounds only the VISIBLE branching: its single
-- finiteness field is
--
--     chan-supp  : List (AnyTypes E)
--     chan-compl : force t ≡ react v τc → ∀ at a → Is-just (v at a) → at ∈ chan-supp
--
-- which mentions the visible offer map `v` alone.  The τ-branch map `τc` is
-- constrained by nothing but a DECISION `stable? : Dec (isStable t)` — and, as
-- `Semantics.FinBr`'s own header explains, the τ-support deliberately CANNOT be
-- enumerated, because τ-indices go through `ExtI.fin`, which is ℕ-polymorphic.
-- But the counterexample's unbounded branching is entirely on τ: `Pinf` is ONE
-- `react` node with `∅v` (no visible offers at all — so `chan-supp = []`, the
-- smallest possible) and an ℕ-indexed τ-branch map.  `FinBr` therefore says
-- nothing about it.
--
-- THE MACHINE-CHECKED EVIDENCE is `finBr-Pinf : FinBr Pinf` below: the exact
-- process that refutes the unconditional law carries a `FinBr` certificate, so
-- adding `FinBr P` as a hypothesis rules nothing out and the conjectured law is
-- false for precisely the same reason the unconditional one is.
--
-- `Pinf`, `chain` and their inversions are reused verbatim from
-- `CSP.Laws.FSim.HideCounterexample`; `finBr-Stop` / `finBr-prefix₀` come from
-- `CSP.Priority.Closure`.
--
-- ZERO postulates, no NON_TERMINATING, no sized types, no holes.
------------------------------------------------------------------------

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.HideMonoFinBrFail where
open PTree

open import CSP.Laws.FSim.HideCounterexample
  using (Ev; h; c; Ev-≟; Rt; chain; Pinf; chainBranches)
open import CSP.Operators Ev-≟ using (Stop; Prefix₀; ∅v)
open import Semantics.LTS {E = Ev} {I = ExtI Ev} using (sRet; sSil; sVis; sTau)
open import CSP.Priority.Base {E = Ev} using (FinBr)
open import CSP.Priority.Closure Ev-≟ using (finBr-Stop; finBr-prefix₀)

------------------------------------------------------------------------
-- Step 1 — every FINITE approximant is finitary (nothing surprising here).
------------------------------------------------------------------------

-- `hⁿ ; STOP` carries a `FinBr`: `STOP` is stable with empty offer support and
-- each prefix adds exactly the single channel `h`.
finBr-chain : ∀ n → FinBr (chain n)
finBr-chain zero    = finBr-Stop
finBr-chain (suc n) = finBr-prefix₀ {e = h} (finBr-chain n)

------------------------------------------------------------------------
-- Step 2 — so is the INFINITELY τ-BRANCHING choice.  This is the point.
------------------------------------------------------------------------

-- `Pinf` is not stable: branch `0` of the ℕ-indexed τ-map is enabled, and ONE
-- enabled τ is all `Dec (isStable ·)` ever needs (it is never an enumeration).
¬stable-Pinf : ¬ (isStable Pinf)
¬stable-Pinf st with st (ℕ , base c) zero
... | ()

-- THE HEADLINE.  The process whose unbounded τ-fan-out refutes unconditional
-- hide monotonicity nevertheless satisfies `FinBr`, with the SMALLEST possible
-- visible support (`chan-supp = []`, as `Pinf` offers `∅v`).  Each τ-successor
-- is some `chain n`, discharged by `finBr-chain`.  Hence a `FinBr` hypothesis on
-- the refining side does not exclude the counterexample.
finBr-Pinf : FinBr Pinf
FinBr.stable?   finBr-Pinf = no ¬stable-Pinf          -- τ-branch `base c` at 0 is enabled
FinBr.chan-supp finBr-Pinf = []                       -- ∅v offers no channel whatsoever
FinBr.chan-compl finBr-Pinf refl at a ()              -- ∅v at a = nothing ⇒ never Is-just
FinBr.next finBr-Pinf (sRet ())                       -- force Pinf = react ≢ ret
FinBr.next finBr-Pinf (sSil ())                       -- react ≢ sil
FinBr.next finBr-Pinf (sVis refl ())                  -- v = ∅v ⇒ `nothing ≡ just` absurd
-- the only real successors: τ-branch `base c` at `n` commits to `hⁿ ; STOP`
FinBr.next finBr-Pinf (sTau {i = _ , base c}   {a = n} refl refl) = finBr-chain n
FinBr.next finBr-Pinf (sTau {i = _ , base h}           refl ())
FinBr.next finBr-Pinf (sTau {i = _ , pair _ _}         refl ())
FinBr.next finBr-Pinf (sTau {i = _ , fin}              refl ())

------------------------------------------------------------------------
-- Step 3 — the certificate really is about the INFINITE branching, not a
-- degenerate reading of `Pinf`.
------------------------------------------------------------------------

-- `Pinf`'s visible support is empty yet it has a distinct τ-successor for EVERY
-- natural number, so `chan-supp` bounds nothing relevant: the two facts coexist.
Pinf-supp-empty : FinBr.chan-supp finBr-Pinf ≡ []
Pinf-supp-empty = refl

-- and the certificate does propagate to each of those infinitely many branches
Pinf-next-chain : ∀ n → FinBr (chain n)
Pinf-next-chain n = FinBr.next finBr-Pinf (sTau {i = ℕ , base c} {a = n} refl refl)
