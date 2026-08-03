{-# OPTIONS --guardedness #-}

-- THE FD HIDING COUNTEREXAMPLE IS NOT A FAILURE SIMULATION.
--
-- `CSP.Laws.FD.HideMonoFD`'s header explains why the UNCONDITIONAL FD law
-- `P ⊑FD Q → (P ∖ A) ⊑FD (Q ∖ A)` is FALSE, via the pair
--
--     Q = μX. h → X          (the IMPLEMENTATION: performs `h` forever)
--     P = ⊓ₙ (hⁿ ; STOP)     (the SPECIFICATION: an infinitely-branching internal
--                             choice — one `react` node whose τ-branch map is `just`
--                             on an ℕ-indexed family of finite `h`-chains)
--
-- for which `P ⊑FD Q` holds but `(P ∖ {h}) ⊑FD (Q ∖ {h})` fails (`Q ∖ {h}` diverges,
-- `P ∖ {h}` cannot — infinite branching defeats König).
--
-- `CSP.Laws.FSim.HideCong.Hide-fsim` proves the corresponding congruence for the
-- OPERATIONAL relation `FSim` with NO side condition.  This module discharges the
-- obligation that comes with that stronger claim: the pair above cannot be used to
-- refute `Hide-fsim`, because it is not an `FSim` in the first place.  The headline is
--
--     ¬fsim-Pinf-Qh : ¬ (FSim Rt Qh Pinf)
--
-- (`FSim R impl spec`, so `Qh` is the impl and `Pinf` the spec, matching
-- `fsim→⊑FD : FSim R Q P → P ⊑FD Q`.)
--
-- ⚠ THE ARGUMENT MUST BE STATE-INDEXED, NOT TRACE-LEVEL.  `Qh` and `Pinf` have exactly
-- the same traces — every `hᵏ` (`Qh-trace` / `Pinf-trace` below prove both inclusions on
-- that family) — so `fsim→⊑T` yields no contradiction whatsoever and no trace argument
-- can work.  What fails is a per-STATE obligation: `WSimF.on-ev` must match `Qh`'s
-- `h`-step by a WEAK `h`-step of the spec, and any such step of `Pinf` must first commit
-- (by a τ) to ONE branch `hⁿ ; STOP` and then land in the residual `h^(n-1) ; STOP`; the
-- simulation is then required to hold at that pair, and `¬fsim-chain` refutes it by
-- induction on `n`.  The impl's residual after `h` is `Qh` again, so the spec's budget
-- strictly decreases while the impl's does not.
--
-- WHAT IS *NOT* FORMALISED HERE: that `Pinf ⊑FD Qh` genuinely holds in the denotational
-- model (the FD half of `HideMonoFD`'s header).  That is a much larger development and
-- its absence does not weaken this result: refuting `Hide-fsim` would require producing
-- an `FSim` for this pair, and that is exactly what is shown impossible.
--
-- NON-VACUITY.  The module also proves that the two processes are the ones intended and
-- are genuinely close: `Qh-unfold` (`Qh` really is `h ⟶₀ Qh`), `Qh-h` (`Qh` really can do
-- `h`, returning to itself), `chain-h` / `chain-trace` (`chain n` really performs exactly
-- `n` `h`s), `Qh-trace` / `Pinf-trace` (both have every trace `hᵏ`), `fsim-Qh-Qh` (`Qh` is
-- `FSim`-relatable at all) and — the sharpest — `fsim-chain-Pinf` : `Pinf` DOES failure-
-- simulate EVERY finite chain `hⁿ ; STOP`.  So the negative result isolates precisely the
-- infinite behaviour and is not true for a boring reason.
--
-- ZERO postulates, no NON_TERMINATING, no sized types, no holes.

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FSim.HideCounterexample where
open PTree

-------------------------------------------------------------------------------------
-- A concrete alphabet.
-------------------------------------------------------------------------------------

-- `h` is the event the FD counterexample hides; it carries `⊤` because a visible offer
-- can only ever FIRE when its carried type is inhabited.  `c` carries `ℕ` and exists
-- solely to supply an INFINITE τ-branch index (`base c : ExtI Ev ℕ`), which is what makes
-- the internal choice `Pinf` infinitely branching.
data Ev : Set → Set where
  h : Ev ⊤
  c : Ev ℕ

-- decidable equality on the alphabet, as `CSP.Operators` requires
Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , h) (_ , h) = yes refl
Ev-≟ (_ , c) (_ , c) = yes refl
Ev-≟ (_ , h) (_ , c) = no λ ()
Ev-≟ (_ , c) (_ , h) = no λ ()

open import CSP.Operators Ev-≟ using (Stop; Prefix; Prefix₀; Prefix-cont; ∅v; ∅t)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
  using ( _─[_]─►_; Label; ev; τ; Event; evLabel; Event√; evl; √
        ; sRet; sSil; sVis; sTau; ev-inv; τ-inv; Diverges)
open import Semantics.WeakBisim {E = Ev} {I = ExtI Ev}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.Failures {E = Ev} {I = ExtI Ev}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.FailureSim {E = Ev} {I = ExtI Ev} using (FSim; fsim-refl)

-- the (irrelevant) return type: none of these processes ever terminates
Rt : Set
Rt = ⊤

-- the single visible label used throughout: the event `h` carrying its only value
evh : Event√ Rt
evh = evl (evLabel ⊤ h tt)

-------------------------------------------------------------------------------------
-- The two processes.
-------------------------------------------------------------------------------------

-- `chain n` = `hⁿ ; STOP`: performs exactly `n` `h`s and then deadlocks
chain : ℕ → PTree Ev (ExtI Ev) Rt
chain zero    = Stop
chain (suc n) = h ⟶₀ chain n

-- `Qh` = `μX. h → X`, the IMPLEMENTATION.  Forward-declared together with its own offer
-- map (rather than written `h ⟶₀ Qh`) because the corecursive occurrence must sit
-- syntactically under a CONSTRUCTOR: passing `Qh` to the defined function `Prefix-cont`
-- is rejected by the productivity checker, whereas `just Qh` inside `Qh-cont` is fine.
-- `Qh-cont-≡` below certifies that `Qh` nevertheless is exactly `h ⟶₀ Qh`.
Qh      : PTree Ev (ExtI Ev) Rt
Qh-cont : (at : AnyTypes Ev) → ContinueType at (Maybe (PTree Ev (ExtI Ev) Rt))

force Qh = react Qh-cont ∅t
Qh-cont (_ , h) tt = just Qh
Qh-cont (_ , c) _  = nothing

-- the τ-branch map of the infinite internal choice: branch `n` (on the ℕ-carrying index
-- `base c`) leads to `hⁿ ; STOP`; every other index is absent
chainBranches : (i : AnyTypes (ExtI Ev))
              → ContinueType i (Maybe (PTree Ev (ExtI Ev) Rt))
chainBranches (_ , base c)   n = just (chain n)
chainBranches (_ , base h)   _ = nothing
chainBranches (_ , pair _ _) _ = nothing
chainBranches (_ , fin)      _ = nothing

-- `Pinf` = `⊓ₙ (hⁿ ; STOP)`, the SPECIFICATION: a single `react` node with NO visible
-- offers and one τ-branch per natural number
Pinf : PTree Ev (ExtI Ev) Rt
force Pinf = react ∅v chainBranches

-------------------------------------------------------------------------------------
-- Sanity: the processes really are what the names claim.
-------------------------------------------------------------------------------------

-- `Qh` really is `μX. h → X`: its offer map agrees POINTWISE with the one `h ⟶₀ Qh`
-- installs (they are not judgementally equal only because the productivity checker
-- forced the map to be written out by hand rather than built by `Prefix-cont`).
Qh-cont-≡ : ∀ at a → Qh-cont at a ≡ Prefix-cont h (λ _ → Qh) at a
Qh-cont-≡ (_ , h) tt = refl
Qh-cont-≡ (_ , c) _  = refl

-- `chain 0` really is `STOP`
chain0-Stop : chain zero ≡ Stop
chain0-Stop = refl

-- `Qh` can perform `h`, and its residual is `Qh` itself (so its budget never decreases)
Qh-h : Qh ─[ ev evh ]─► Qh
Qh-h = sVis {at = ⊤ , h} {a = tt} refl refl

-- `hⁿ⁺¹ ; STOP` can perform `h`, with residual `hⁿ ; STOP`
chain-h : ∀ n → chain (suc n) ─[ ev evh ]─► chain n
chain-h n = sVis {at = ⊤ , h} {a = tt} refl refl

-- `Pinf` can commit, by a τ, to any branch `hⁿ ; STOP`
Pinf-τ→chain : ∀ n → Pinf ─[ τ ]─► chain n
Pinf-τ→chain n = sTau {i = ℕ , base c} {a = n} refl refl

-------------------------------------------------------------------------------------
-- Inversions.  (`chain n` is τ-free and offers only `h`; `Pinf` is visible-free.)
-------------------------------------------------------------------------------------

-- no chain has a τ-move: its τ-branch map is everywhere `nothing`
chain-noτ : ∀ n {t : PTree Ev (ExtI Ev) Rt} → chain n ─[ τ ]─► t → ⊥
chain-noτ zero    (sSil ())
chain-noτ zero    (sTau refl ())
chain-noτ (suc n) (sSil ())
chain-noτ (suc n) (sTau refl ())

-- hence a τ*-run out of a chain is the empty one
chain-τ*-inv : ∀ n {t : PTree Ev (ExtI Ev) Rt} → chain n ─[τ*]─► t → t ≡ chain n
chain-τ*-inv n τ*-refl        = refl
chain-τ*-inv n (τ*-step s _)  = ⊥-elim (chain-noτ n s)

-- `STOP` offers nothing, in particular not `h`
chain0-noEv : ∀ {t : PTree Ev (ExtI Ev) Rt} → chain zero ─[ ev evh ]─► t → ⊥
chain0-noEv step with ev-inv step
... | v , τc , refl , ()

-- the only `h`-residual of `hⁿ⁺¹ ; STOP` is `hⁿ ; STOP`
chain-ev-inv : ∀ n {t : PTree Ev (ExtI Ev) Rt}
             → chain (suc n) ─[ ev evh ]─► t → t ≡ chain n
chain-ev-inv n step with ev-inv step
... | v , τc , refl , refl = refl

-- FULL visible inversion for a chain: any visible step is an `h`-step of a successor
-- chain.  (Needed for `fsim-chain-Pinf`, where the label is not fixed in advance.)
chain-ev-inv′ : ∀ n {l : Event√ Rt} {t : PTree Ev (ExtI Ev) Rt}
              → chain n ─[ ev l ]─► t
              → Σ[ m ∈ ℕ ] (n ≡ suc m × l ≡ evh × t ≡ chain m)
chain-ev-inv′ zero    (sRet ())
chain-ev-inv′ zero    (sVis refl ())
chain-ev-inv′ (suc m) (sRet ())
chain-ev-inv′ (suc m) (sVis {at = _ , h} {a = tt} refl refl) = m , refl , refl , refl
chain-ev-inv′ (suc m) (sVis {at = _ , c} refl ())

-- every τ-move of the infinite choice commits to some branch
Pinf-τ-inv : ∀ {t : PTree Ev (ExtI Ev) Rt} → Pinf ─[ τ ]─► t → Σ[ n ∈ ℕ ] (t ≡ chain n)
Pinf-τ-inv step with τ-inv step
... | inj₁ ()
... | inj₂ (v , τc , (_ , base c)   , n , refl , refl) = n , refl
... | inj₂ (v , τc , (_ , base h)   , _ , refl , ())
... | inj₂ (v , τc , (_ , pair _ _) , _ , refl , ())
... | inj₂ (v , τc , (_ , fin)      , _ , refl , ())

-- KEY τ*-INVERSION: a τ*-run out of the infinite choice either stays at the choice node
-- or commits to exactly one branch (and then stops, since chains are τ-free)
Pinf-τ*-inv : ∀ {t : PTree Ev (ExtI Ev) Rt}
            → Pinf ─[τ*]─► t → (t ≡ Pinf) ⊎ Σ[ n ∈ ℕ ] (t ≡ chain n)
Pinf-τ*-inv τ*-refl = inj₁ refl
Pinf-τ*-inv (τ*-step s rest) with Pinf-τ-inv s
... | n , refl = inj₂ (n , chain-τ*-inv n rest)

-- the infinite choice offers no visible event at all
Pinf-noEv : ∀ {t : PTree Ev (ExtI Ev) Rt} → Pinf ─[ ev evh ]─► t → ⊥
Pinf-noEv step with ev-inv step
... | v , τc , refl , ()

-------------------------------------------------------------------------------------
-- THE REFUTATION.
-------------------------------------------------------------------------------------

-- KEY LEMMA, by induction on `n`: a FINITE chain cannot failure-simulate the impl that
-- performs `h` forever.  At `0` the spec cannot match the impl's `h` at all; at `n+1`
-- the only weak `h`-match lands in `hⁿ ; STOP` (chains are τ-free, so both τ*-padding
-- runs are empty) while the impl is back at `Qh` — which is the induction hypothesis.
¬fsim-chain : ∀ n → ¬ (FSim Rt Qh (chain n))
¬fsim-chain zero sim with sim .FSim.fwd .WSimF.on-ev Qh-h
... | _ , wev pre step post , _ with chain-τ*-inv zero pre
...   | refl = chain0-noEv step
¬fsim-chain (suc n) sim with sim .FSim.fwd .WSimF.on-ev Qh-h
... | _ , wev pre step post , sim′ with chain-τ*-inv (suc n) pre
...   | refl with chain-ev-inv n step
...     | refl with chain-τ*-inv n post
...       | refl = ¬fsim-chain n sim′

-- HEADLINE: the FD hiding counterexample pair is NOT a failure simulation, so it cannot
-- be fed to `CSP.Laws.FSim.HideCong.Hide-fsim` and does not refute it.  The impl's first
-- `h` must be matched weakly by the spec; the leading τ*-run out of `Pinf` either stays
-- at the (visible-free) choice node or commits to one branch, and in the latter case the
-- residual pair is refuted by `¬fsim-chain`.
¬fsim-Pinf-Qh : ¬ (FSim Rt Qh Pinf)
¬fsim-Pinf-Qh sim with sim .FSim.fwd .WSimF.on-ev Qh-h
... | _ , wev pre step post , sim′ with Pinf-τ*-inv pre
...   | inj₁ refl            = Pinf-noEv step
...   | inj₂ (zero  , refl)  = chain0-noEv step
...   | inj₂ (suc n , refl) with chain-ev-inv n step
...     | refl with chain-τ*-inv n post
...       | refl = ¬fsim-chain n sim′

-------------------------------------------------------------------------------------
-- NON-VACUITY.  The two processes are trace-equivalent on the `hᵏ` family, and the spec
-- DOES failure-simulate every finite approximant — so the refutation above is about the
-- infinite behaviour alone.
-------------------------------------------------------------------------------------

-- the trace `hᵏ`
hTrace : ℕ → List (Event√ Rt)
hTrace zero    = []
hTrace (suc n) = evh ∷ hTrace n

-- `hⁿ ; STOP` really performs exactly `n` `h`s, ending in `STOP`
chain-trace : ∀ n → chain n ⟹⟨ hTrace n ⟩ chain zero
chain-trace zero    = ⟹-refl
chain-trace (suc n) = ⟹-ev (chain-h n) (chain-trace n)

-- the impl has every trace `hᵏ`
Qh-trace : ∀ n → Qh ⟹⟨ hTrace n ⟩ Qh
Qh-trace zero    = ⟹-refl
Qh-trace (suc n) = ⟹-ev Qh-h (Qh-trace n)

-- …and so does the spec: commit to branch `n`, then run that chain out.  Together with
-- `Qh-trace` this shows a pure TRACE argument can never separate the two.
Pinf-trace : ∀ n → Pinf ⟹⟨ hTrace n ⟩ chain zero
Pinf-trace n = ⟹-τ (Pinf-τ→chain n) (chain-trace n)

-- the impl is `FSim`-relatable at all (so `¬fsim-Pinf-Qh` is not about `Qh` being junk)
fsim-Qh-Qh : FSim Rt Qh Qh
fsim-Qh-Qh = fsim-refl Qh

-- the forward half of `fsim-chain-Pinf`: a chain's only move is an `h`, matched by
-- committing to the corresponding branch and firing its head event
f-chain-Pinf : ∀ n → WSimF (FSim Rt) (chain n) Pinf
f-chain-Pinf n .WSimF.on-ev step with chain-ev-inv′ n step
... | m , refl , refl , refl =
      chain m
    , wev (τ*-step (Pinf-τ→chain (suc m)) τ*-refl) (chain-h m) τ*-refl
    , fsim-refl (chain m)
f-chain-Pinf n .WSimF.on-tau step = ⊥-elim (chain-noτ n step)

-- THE POSITIVE COUNTERPART: the very same spec DOES failure-simulate every finite
-- `hⁿ ; STOP` (settle on branch `n` and copy it).  Hence `¬fsim-Pinf-Qh` fails for no
-- structural reason — it isolates exactly the impl's unbounded `h`-behaviour.
fsim-chain-Pinf : ∀ n → FSim Rt (chain n) Pinf
fsim-chain-Pinf n .FSim.fwd     = f-chain-Pinf n
fsim-chain-Pinf n .FSim.stab st =
  chain n , τ*-step (Pinf-τ→chain n) τ*-refl , st , λ _ off → off
fsim-chain-Pinf n .FSim.div→  d = ⊥-elim (chain-noτ n (d .Diverges.step))
