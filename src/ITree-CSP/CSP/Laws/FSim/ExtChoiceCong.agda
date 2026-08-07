{-# OPTIONS --guardedness #-}

-- FAILURE-SIMULATION congruence for EXTERNAL CHOICE `_□_`, TWO-SIDED and
-- UNCONDITIONAL:
--
--   □-fsim : FSim R P₁ P₂ → FSim R Q₁ Q₂ → FSim R (P₁ □ Q₁) (P₂ □ Q₂)
--
-- ORIENTATION: in `FSim R t₁ t₂` the FIRST argument is the IMPLEMENTATION and the
-- SECOND the SPECIFICATION (`fsim→⊑FD : FSim R Q P → P ⊑FD Q`).  Unlike `Par-fsim`
-- there is NO `Sep`-style side condition: `□` never needs the operands to be
-- separated, because it does not synchronise — an offer overlap is legal and simply
-- resolves into an internal choice.  `_□_` does need `⦃ DecEq R ⦄` (it compares the
-- two return values to decide whether a doubly-terminated choice is a single `ret`).
--
-- ══ THE PROOF STRATEGY: THE SPEC NEVER MOVES ══
--
-- `Semantics.FailureSim.fsim-τ*-prepend` says a failure simulation survives PREPENDING
-- τ's to the spec, so the spec may be LAZY: every impl τ is matched by the EMPTY spec
-- run and the spec sits at `P₂ □ Q₂` for the whole life of the context.  The invariant
-- carried instead is the pair of τ*-runs that the spec OWES:
--
--     (P₂ ─[τ*]─► P₂′) × (Q₂ ─[τ*]─► Q₂′) × FSim R P₁ P₂′ × FSim R Q₁ Q₂′
--
-- and the debt is discharged only where the spec must genuinely act — a visible step,
-- a √, or `stab`.  This is what makes the law provable at all:
--
--   * the SPEC is never itself in a `▷` state at a residual pair.  Residuals are MIXED
--     pairs, impl `▷` against spec `□`.  Therefore the TWO-SIDED `▷` congruence is
--     never invoked — which matters, because it is FALSE and formally refuted in
--     `CSP.Laws.FSim.SlideCounterexample.¬▷-fsim`.
--   * the debt runs are lifted through `□` only at points where the disjunction of
--     `ExtChoiceLift.□-τ*-L` is immediately absorbed (a visible step dissolves both the
--     choice and the slide onto the same successor) or where `NonRet` is available for
--     free (`stab`: a settle target is stable, hence never a `ret`).
--
-- ══ THE FOUR IMPL SHAPES ══
--
-- The impl side of the invariant ranges over four shapes, and they form a
-- mutually-recursive family (declared up front — no old-style `mutual` block):
--
--   S1  `P₁ □ Q₁`   — `□-fsim-run`.  τ's are inverted by the reused FORCE-CARRYING
--                     `□-τ-inv-full` (the plain `□-τ-elim` drops exactly the `ret`
--                     witnesses that decide which shape the residual is), giving:
--                     commit-to-a-terminated-operand → S4; choice → S1; slide → S2/S3.
--   S2  `A ▷ Q₁`    — `▷□-fsim-L`, `force Q₁ ≡ ret r` (the right operand terminated,
--                     so it became a TIMEOUT).  `stab` is VACUOUS (`▷-unstable`), and
--                     `div→` decomposes because the timeout lands on a `ret`: a dead
--                     end, so only the live side can carry the livelock.
--   S3  `B ▷ P₁`    — `▷□-fsim-R`, the mirror (`force P₁ ≡ ret r`).  Note the operands
--                     SWAP: `□-τ-inv-full`'s `sQP` shape is `Q′ ▷ P`.
--   S4  a bare `ret` operand — `ret-fsim`, NOT recursive: only `√` remains, `stab` and
--                     `div→` are absurd.  The spec discharges it with a WEAK √
--                     (`□-w√-L/-R`): the composite generally has to τ-commit first.
--
-- Also: the replicated folds `□Fin-fsim` / `□⋆-fsim` (one line each — unlike
-- `⦀Fin-fsim`, no side condition has to be threaded through the fold).
--
-- `stab` is markedly cheaper than `Par`'s three-way split: `□-stable-elim` gives
-- exactly `isStable P₁ × isStable Q₁` — ONE leaf, no `ret` cases, since a `□` with a
-- terminated operand is never stable.  Each spec operand settles by its own
-- `FSim.stab`; the two settle runs interleave with `□-τ*-settle` and recombine with
-- `stable-□` + `□-offer-mono`.
--
-- POSTULATES: none declared locally.  USED: exactly TWO, both from
-- `CSP.Laws.FD.ExtChoiceDivergence`, both certified sound from the single `dne` of
-- `CSP.Laws.ClassicalFromLEM`, and both consumed ONLY by the `div→` fields (`fwd` and
-- `stab` are fully constructive) — `□-Diverges→` (one site, `□-run-div→`) and
-- `▷-Diverges→` (two sites, `▷□-L-div→` and `▷□-R-div→`, the S2/S3 mirrors), each
-- deciding which operand carries an impl livelock via the classical infinite-pigeonhole
-- step.
--
-- CLOSURE IS NOW TIGHT.  The transitive import closure carries exactly ONE
-- postulate-bearing module, `CSP.Laws.FD.ExtChoiceDivergence`, and that module declares
-- exactly the two postulates named above — so every postulate reachable from here is one
-- this proof genuinely uses.  It previously carried TEN, the other nine
-- (`Semantics.DRImpliesFD`, `CSP.Laws.Bisim.DRCongruence`, `CSP.Laws.FD.FDTransfer`,
-- `CSP.Laws.FD.HideDivergence`, `CSP.Laws.FD.InterruptDivergence`,
-- `CSP.Laws.FD.IterateFD`, `CSP.Laws.FD.ParallelDivergence`,
-- `CSP.Laws.FD.ParallelRefusals`, `CSP.Laws.FD.SeqDistR`) pulled in by a single edge —
-- `CSP.Laws.Stability.Closure`, the whole-stability-layer SURVEY, imported merely to
-- borrow two `□`-specific facts.  Those two facts now live in
-- `CSP.Laws.Stability.ExtChoice` (moved verbatim; the survey re-exports them, so its
-- other clients are unaffected), whose own closure is postulate-bearing only through
-- `ExtChoiceFD` → `ExtChoiceDivergence` — already a direct import here, so the borrow
-- costs nothing.
--
-- STILL NOT `--safe`: `agda --safe CSP/Laws/FSim/ExtChoiceCong.agda` fails with two
-- `SafeFlagPostulate` errors, one per genuinely-used name.  That is irreducible without
-- discharging the two classical inversions themselves; "closure contains only the
-- postulates this proof uses" is the achievable and now-achieved goal.
-- No NON_TERMINATING, no sized types, no holes.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
  renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FSim.ExtChoiceCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS        {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.DRBisim    {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Refusals   {E = E} {I = ExtI E} using (Offers)
open import Semantics.FailureSim {E = E} {I = ExtI E}
  using (FSim; fsim-refl; fsim-τ*-prepend; div-prepend-τ*; fsim→⊑FD)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_⊑FD_)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-τ-inv; ⊓-stepL; ⊓-stepR)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (□-ev-elim; evP; evQ; evPQ; ▷-τ-elim; ▷-ev-elim; ret-no-τ)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (□-Diverges-L; □-Diverges-R; ▷-unstable; stable-not-ret; stable-no-τ)
open import CSP.Laws.FD.ExtChoiceAssoc E-≟ using (□-τ-inv-full)
open import CSP.Laws.FD.ExtChoiceDivergence E-≟ using (□-Diverges→; ▷-Diverges→)
open import CSP.Laws.Stability.ExtChoice E-≟ using (stable-□; □-stable-elim)
open import CSP.Laws.FSim.IChoiceCong E-≟ using (⊓-fsim)
open import CSP.Laws.FSim.ExtChoiceLift E-≟
  using (□-wev-L; □-wev-R; □-w√-L; □-w√-R; □-wev-LR; □-τ*-settle; □-offer-mono)

-------------------------------------------------------------------------------------
-- GENERIC PLUMBING.  Two `FSim` facts that are not about `□` at all, needed to close
-- the S4 leaf and the doubly-terminated overlap; kept here rather than in
-- `Semantics.FailureSim` / `IChoiceCong` so that no existing module is touched.
-------------------------------------------------------------------------------------

-- pay a τ*-debt in front of a weak visible step (the spec's owed silent run)
wev-τ*-pre : ∀ {ℓr} {R : Set ℓr} {t u v : PTree E (ExtI E) R} {l : Event√ R}
           → t ─[τ*]─► u → u ═[ ev l ]═► v → t ═[ ev l ]═► v
wev-τ*-pre run (wev pre step post) = wev (τ*-trans run pre) step post

-- S4: a TERMINATED impl is failure-simulated by anything that can weakly √ on the same
-- value and then dominate the residual `deadlock`.  All three other obligations are
-- absurd for a `ret` node: it has no τ (so no divergence) and is never stable
ret-fsim : ∀ {ℓr} {R : Set ℓr} {T S Y : PTree E (ExtI E) R} {r : R}
         → PTree.force T ≡ ret r → S ═[ ev (√ r) ]═► Y → FSim R deadlock Y
         → FSim R T S
ret-fsim {T = T} eqT w sim .FSim.fwd .WSimF.on-ev (sRet eq) with trans (sym eq) eqT
... | refl = _ , w , sim
-- a `ret` node has no visible offer at all
ret-fsim {T = T} eqT w sim .FSim.fwd .WSimF.on-ev (sVis eq _) with trans (sym eqT) eq
... | ()
ret-fsim {T = T} eqT w sim .FSim.fwd .WSimF.on-tau step = ⊥-elim (ret-no-τ eqT step)
ret-fsim {T = T} eqT w sim .FSim.stab st = ⊥-elim (stable-not-ret {t = T} eqT st)
ret-fsim {T = T} eqT w sim .FSim.div→ d = ⊥-elim (ret-no-τ eqT (d .Diverges.step))

-- an INTERNAL CHOICE is failure-simulated by any spec that dominates BOTH branches
-- (the impl's own nondeterminism, so the spec need not move at all).  Used for the
-- degenerate overlap where both operands offer the SAME √
⊓-fsim-join : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {T₁ T₂ S : PTree E (ExtI E) R}
            → FSim R T₁ S → FSim R T₂ S → FSim R (T₁ ⊓ T₂) S

-- the forward half: a τ of the impl choice commits to one branch, matched by the empty
-- spec run and that branch's own simulation
f-sim-⊓-join : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {T₁ T₂ S : PTree E (ExtI E) R}
             → FSim R T₁ S → FSim R T₂ S → WSimF (FSim R) (T₁ ⊓ T₂) S
f-sim-⊓-join s₁ s₂ .WSimF.on-ev (sRet ())
f-sim-⊓-join s₁ s₂ .WSimF.on-ev (sVis refl ())
f-sim-⊓-join {T₁ = T₁} {T₂ = T₂} {S = S} s₁ s₂ .WSimF.on-tau step
  with ⊓-τ-inv T₁ T₂ step
... | inj₁ refl = S , wτ τ*-refl , s₁
... | inj₂ refl = S , wτ τ*-refl , s₂

⊓-fsim-join s₁ s₂ .FSim.fwd = f-sim-⊓-join s₁ s₂
-- `isStable (T₁ ⊓ T₂)` is absurd: the left τ-branch always fires
⊓-fsim-join {T₁ = T₁} {T₂ = T₂} s₁ s₂ .FSim.stab st =
  ⊥-elim (stable-no-τ st (⊓-stepL T₁ T₂))
-- a livelock of the impl choice runs through one branch, so that branch's `div→` takes it
⊓-fsim-join {T₁ = T₁} {T₂ = T₂} s₁ s₂ .FSim.div→ d with ⊓-τ-inv T₁ T₂ (d .Diverges.step)
... | inj₁ eq = s₁ .FSim.div→ (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = s₂ .FSim.div→ (subst Diverges eq (d .Diverges.rest))

-------------------------------------------------------------------------------------
-- FORWARD DECLARATIONS for the four-shape family (no old-style `mutual`).  Every
-- corecursive call sits under the `_,_` of a `WSimF` Σ-result — the discipline
-- `SlideCong.f-sim-▷-R` / `HideCong.f-sim-∖` use — and no composite is ever
-- `with`-forced at a call site: operands go to the lift lemmas as ARGUMENTS.
-------------------------------------------------------------------------------------

-- S1: the choice itself, with the spec's owed silent runs carried in the invariant
□-fsim-run : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {P₁ Q₁ : PTree E (ExtI E) R}
             (P₂ Q₂ : PTree E (ExtI E) R) {P₂′ Q₂′ : PTree E (ExtI E) R}
           → P₂ ─[τ*]─► P₂′ → Q₂ ─[τ*]─► Q₂′
           → FSim R P₁ P₂′ → FSim R Q₁ Q₂′
           → FSim R (P₁ □ Q₁) (P₂ □ Q₂)

-- S2: the RIGHT operand terminated, so the impl slid into `A ▷ Q₁` with `Q₁` the timeout
▷□-fsim-L : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {A Q₁ : PTree E (ExtI E) R}
            (P₂ Q₂ : PTree E (ExtI E) R) {P₂′ Q₂′ : PTree E (ExtI E) R} {r : R}
          → PTree.force Q₁ ≡ ret r
          → P₂ ─[τ*]─► P₂′ → Q₂ ─[τ*]─► Q₂′
          → FSim R A P₂′ → FSim R Q₁ Q₂′
          → FSim R (A ▷ Q₁) (P₂ □ Q₂)

-- S3: the LEFT operand terminated, so the impl slid into `B ▷ P₁` (operands swapped)
▷□-fsim-R : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {P₁ B : PTree E (ExtI E) R}
            (P₂ Q₂ : PTree E (ExtI E) R) {P₂′ Q₂′ : PTree E (ExtI E) R} {r : R}
          → PTree.force P₁ ≡ ret r
          → P₂ ─[τ*]─► P₂′ → Q₂ ─[τ*]─► Q₂′
          → FSim R P₁ P₂′ → FSim R B Q₂′
          → FSim R (B ▷ P₁) (P₂ □ Q₂)

-- the forward half of S1
f-sim-□-run : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {P₁ Q₁ : PTree E (ExtI E) R}
              (P₂ Q₂ : PTree E (ExtI E) R) {P₂′ Q₂′ : PTree E (ExtI E) R}
            → P₂ ─[τ*]─► P₂′ → Q₂ ─[τ*]─► Q₂′
            → FSim R P₁ P₂′ → FSim R Q₁ Q₂′
            → WSimF (FSim R) (P₁ □ Q₁) (P₂ □ Q₂)

-- the forward half of S2
f-sim-▷□-L : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {A Q₁ : PTree E (ExtI E) R}
             (P₂ Q₂ : PTree E (ExtI E) R) {P₂′ Q₂′ : PTree E (ExtI E) R} {r : R}
           → PTree.force Q₁ ≡ ret r
           → P₂ ─[τ*]─► P₂′ → Q₂ ─[τ*]─► Q₂′
           → FSim R A P₂′ → FSim R Q₁ Q₂′
           → WSimF (FSim R) (A ▷ Q₁) (P₂ □ Q₂)

-- the forward half of S3
f-sim-▷□-R : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {P₁ B : PTree E (ExtI E) R}
             (P₂ Q₂ : PTree E (ExtI E) R) {P₂′ Q₂′ : PTree E (ExtI E) R} {r : R}
           → PTree.force P₁ ≡ ret r
           → P₂ ─[τ*]─► P₂′ → Q₂ ─[τ*]─► Q₂′
           → FSim R P₁ P₂′ → FSim R B Q₂′
           → WSimF (FSim R) (B ▷ P₁) (P₂ □ Q₂)

-------------------------------------------------------------------------------------
-- THE `div→` FIELDS.  Not corecursive — each only splits the impl livelock with the
-- certified König step, transfers it through the guilty operand's own `div→`, pays the
-- spec's τ*-debt in front of it (`div-prepend-τ*`) and re-lifts with the CONSTRUCTIVE
-- `□-Diverges-L/-R`.  In S2/S3 the timeout side is a `ret`, a dead end, so the split
-- has only one live branch.
-------------------------------------------------------------------------------------

-- S1's livelock transfer
□-run-div→ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {P₁ Q₁ : PTree E (ExtI E) R}
             (P₂ Q₂ : PTree E (ExtI E) R) {P₂′ Q₂′ : PTree E (ExtI E) R}
           → P₂ ─[τ*]─► P₂′ → Q₂ ─[τ*]─► Q₂′
           → FSim R P₁ P₂′ → FSim R Q₁ Q₂′
           → Diverges (P₁ □ Q₁) → Diverges (P₂ □ Q₂)
□-run-div→ {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq d
  with □-Diverges→ {P = P₁} {Q = Q₁} d
... | inj₁ dP = □-Diverges-L {P = P₂} {Q = Q₂} (div-prepend-τ* runP (pp .FSim.div→ dP))
... | inj₂ dQ = □-Diverges-R {P = P₂} {Q = Q₂} (div-prepend-τ* runQ (qq .FSim.div→ dQ))

-- S2's livelock transfer: the timeout `Q₁` is a `ret` and cannot diverge
▷□-L-div→ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {A Q₁ : PTree E (ExtI E) R}
            (P₂ Q₂ : PTree E (ExtI E) R) {P₂′ : PTree E (ExtI E) R} {r : R}
          → PTree.force Q₁ ≡ ret r
          → P₂ ─[τ*]─► P₂′ → FSim R A P₂′
          → Diverges (A ▷ Q₁) → Diverges (P₂ □ Q₂)
▷□-L-div→ {A = A} {Q₁ = Q₁} P₂ Q₂ eqQ₁ runP pp d with ▷-Diverges→ {P = A} {Q = Q₁} d
... | inj₁ dA  = □-Diverges-L {P = P₂} {Q = Q₂} (div-prepend-τ* runP (pp .FSim.div→ dA))
... | inj₂ dQ₁ = ⊥-elim (ret-no-τ eqQ₁ (dQ₁ .Diverges.step))

-- S3's livelock transfer (mirror: the terminated operand is now `P₁`)
▷□-R-div→ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {P₁ B : PTree E (ExtI E) R}
            (P₂ Q₂ : PTree E (ExtI E) R) {Q₂′ : PTree E (ExtI E) R} {r : R}
          → PTree.force P₁ ≡ ret r
          → Q₂ ─[τ*]─► Q₂′ → FSim R B Q₂′
          → Diverges (B ▷ P₁) → Diverges (P₂ □ Q₂)
▷□-R-div→ {P₁ = P₁} {B = B} P₂ Q₂ eqP₁ runQ qq d with ▷-Diverges→ {P = B} {Q = P₁} d
... | inj₁ dB  = □-Diverges-R {P = P₂} {Q = Q₂} (div-prepend-τ* runQ (qq .FSim.div→ dB))
... | inj₂ dP₁ = ⊥-elim (ret-no-τ eqP₁ (dP₁ .Diverges.step))

-------------------------------------------------------------------------------------
-- S1's FORWARD HALF.  τ's go through the force-carrying `□-τ-inv-full`; the spec
-- answers every one of them with the EMPTY run (`wτ τ*-refl`) and grows its τ*-debt.
-- Visible steps and √'s are where the debt is paid: prepend it (`wev-τ*-pre`) and lift
-- with `□-wev-L/-R`, which reach exactly the operand's own successor.
-------------------------------------------------------------------------------------

f-sim-□-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .WSimF.on-tau step
  with □-τ-inv-full P₁ Q₁ step
-- COMMIT to a terminated left operand: only its √ remains ⇒ S4
... | inj₁ (rP , eqP₁ , refl) with pp .FSim.fwd .WSimF.on-ev (sRet eqP₁)
...   | _ , wP , simD =
        (P₂ □ Q₂) , wτ τ*-refl
      , ret-fsim eqP₁ (□-w√-L P₂ Q₂ (wev-τ*-pre runP wP)) simD
-- COMMIT to a terminated right operand ⇒ S4
f-sim-□-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .WSimF.on-tau step
  | inj₂ (inj₁ (rQ , eqQ₁ , refl)) with qq .FSim.fwd .WSimF.on-ev (sRet eqQ₁)
...   | _ , wQ , simD =
        (P₂ □ Q₂) , wτ τ*-refl
      , ret-fsim eqQ₁ (□-w√-R P₂ Q₂ (wev-τ*-pre runQ wQ)) simD
-- the LEFT operand's own τ, choice preserved ⇒ S1 (corecursion), left debt grows
f-sim-□-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .WSimF.on-tau step
  | inj₂ (inj₂ (inj₁ (P₁′ , Pτ , refl))) with pp .FSim.fwd .WSimF.on-tau Pτ
...   | _ , wτ run′ , pp′ =
        (P₂ □ Q₂) , wτ τ*-refl , □-fsim-run P₂ Q₂ (τ*-trans runP run′) runQ pp′ qq
-- the RIGHT operand's own τ ⇒ S1, right debt grows
f-sim-□-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .WSimF.on-tau step
  | inj₂ (inj₂ (inj₂ (inj₁ (Q₁′ , Qτ , refl)))) with qq .FSim.fwd .WSimF.on-tau Qτ
...   | _ , wτ run′ , qq′ =
        (P₂ □ Q₂) , wτ τ*-refl , □-fsim-run P₂ Q₂ runP (τ*-trans runQ run′) pp qq′
-- the LEFT operand's τ against a TERMINATED right operand: the choice becomes a slide
-- over the terminated operand ⇒ S2
f-sim-□-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .WSimF.on-tau step
  | inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (P₁′ , rQ , Pτ , eqQ₁ , refl)))))
      with pp .FSim.fwd .WSimF.on-tau Pτ
...   | _ , wτ run′ , pp′ =
        (P₂ □ Q₂) , wτ τ*-refl
      , ▷□-fsim-L P₂ Q₂ eqQ₁ (τ*-trans runP run′) runQ pp′ qq
-- the RIGHT operand's τ against a TERMINATED left operand ⇒ S3 (operands swap)
f-sim-□-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .WSimF.on-tau step
  | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (Q₁′ , rP , Qτ , eqP₁ , refl)))))
      with qq .FSim.fwd .WSimF.on-tau Qτ
...   | _ , wτ run′ , qq′ =
        (P₂ □ Q₂) , wτ τ*-refl
      , ▷□-fsim-R P₂ Q₂ eqP₁ runP (τ*-trans runQ run′) pp qq′

f-sim-□-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .WSimF.on-ev step
  with □-ev-elim P₁ Q₁ step
-- only the LEFT operand offers (the composite √ lands here too, via `□-force-ret-inv`)
... | evP pev with pp .FSim.fwd .WSimF.on-ev pev
...   | Y , wP , sim = Y , □-wev-L P₂ Q₂ (wev-τ*-pre runP wP) , sim
-- only the RIGHT operand offers
f-sim-□-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .WSimF.on-ev step
  | evQ qev with qq .FSim.fwd .WSimF.on-ev qev
...   | Y , wQ , sim = Y , □-wev-R P₂ Q₂ (wev-τ*-pre runQ wQ) , sim
-- BOTH operands offer the same VISIBLE event: the impl lands in `P₁′ ⊓ Q₁′`, so drive
-- BOTH spec operands to `e`-offering states (`□-wev-LR`) and close with `⊓-fsim`, each
-- operand's trailing silent run absorbed by `fsim-τ*-prepend`
f-sim-□-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .WSimF.on-ev step
  | evPQ (sVis {at = at} {a = a} eqfP brP) qev
      with pp .FSim.fwd .WSimF.on-ev (sVis {at = at} {a = a} eqfP brP)
         | qq .FSim.fwd .WSimF.on-ev qev
...   | _ , wev preP stepP postP , simP | _ , wev preQ stepQ postQ , simQ =
        _ , □-wev-LR P₂ Q₂ (τ*-trans runP preP) stepP (τ*-trans runQ preQ) stepQ
          , ⊓-fsim (fsim-τ*-prepend postP simP) (fsim-τ*-prepend postQ simQ)
-- BOTH operands terminate on the same value.  `□-ev-elim` never actually produces this
-- (it routes a composite √ to `evP`), but the `□evR` index does not record that, so it
-- is discharged: the impl residual is `deadlock ⊓ deadlock` and ONE weak spec √ covers
-- both branches (`⊓-fsim-join`)
f-sim-□-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .WSimF.on-ev step
  | evPQ (sRet eqP₁) (sRet eqQ₁) with pp .FSim.fwd .WSimF.on-ev (sRet eqP₁)
...   | Y , wP , simD =
        Y , □-w√-L P₂ Q₂ (wev-τ*-pre runP wP) , ⊓-fsim-join simD simD

-------------------------------------------------------------------------------------
-- S2's FORWARD HALF.  `▷-τ-elim` splits a τ into the TIMEOUT (landing on the
-- terminated `Q₁` ⇒ S4) and the live operand's own τ (⇒ S2 corecursion).  A visible
-- step is inverted by `▷-ev-elim`, which drops the slide entirely and lands on the
-- SAME successor, so it is answered exactly like S1's `evP` case.
-------------------------------------------------------------------------------------

f-sim-▷□-L {A = A} {Q₁ = Q₁} P₂ Q₂ eqQ₁ runP runQ pp qq .WSimF.on-tau step
  with ▷-τ-elim A Q₁ step
-- the TIMEOUT: the impl is now the terminated `Q₁`, whose only move is its √ ⇒ S4
... | inj₁ refl with qq .FSim.fwd .WSimF.on-ev (sRet eqQ₁)
...   | _ , wQ , simD =
        (P₂ □ Q₂) , wτ τ*-refl
      , ret-fsim eqQ₁ (□-w√-R P₂ Q₂ (wev-τ*-pre runQ wQ)) simD
-- a τ OF the live operand: the slide survives with the same timeout ⇒ S2
f-sim-▷□-L {A = A} {Q₁ = Q₁} P₂ Q₂ eqQ₁ runP runQ pp qq .WSimF.on-tau step
  | inj₂ (A′ , Aτ , refl) with pp .FSim.fwd .WSimF.on-tau Aτ
...   | _ , wτ run′ , pp′ =
        (P₂ □ Q₂) , wτ τ*-refl
      , ▷□-fsim-L P₂ Q₂ eqQ₁ (τ*-trans runP run′) runQ pp′ qq

f-sim-▷□-L {A = A} {Q₁ = Q₁} P₂ Q₂ eqQ₁ runP runQ pp qq .WSimF.on-ev step
  with pp .FSim.fwd .WSimF.on-ev (▷-ev-elim A Q₁ step)
... | Y , wP , sim = Y , □-wev-L P₂ Q₂ (wev-τ*-pre runP wP) , sim

-------------------------------------------------------------------------------------
-- S3's FORWARD HALF, the mirror.  The live operand is now the RIGHT one (`B`), so its
-- debt run and its lifts are the `-R` variants, while the timeout `P₁` is the LEFT one.
-------------------------------------------------------------------------------------

f-sim-▷□-R {P₁ = P₁} {B = B} P₂ Q₂ eqP₁ runP runQ pp qq .WSimF.on-tau step
  with ▷-τ-elim B P₁ step
-- the TIMEOUT lands on the terminated LEFT operand ⇒ S4, discharged on the left
... | inj₁ refl with pp .FSim.fwd .WSimF.on-ev (sRet eqP₁)
...   | _ , wP , simD =
        (P₂ □ Q₂) , wτ τ*-refl
      , ret-fsim eqP₁ (□-w√-L P₂ Q₂ (wev-τ*-pre runP wP)) simD
-- a τ OF the live right operand ⇒ S3
f-sim-▷□-R {P₁ = P₁} {B = B} P₂ Q₂ eqP₁ runP runQ pp qq .WSimF.on-tau step
  | inj₂ (B′ , Bτ , refl) with qq .FSim.fwd .WSimF.on-tau Bτ
...   | _ , wτ run′ , qq′ =
        (P₂ □ Q₂) , wτ τ*-refl
      , ▷□-fsim-R P₂ Q₂ eqP₁ runP (τ*-trans runQ run′) pp qq′

f-sim-▷□-R {P₁ = P₁} {B = B} P₂ Q₂ eqP₁ runP runQ pp qq .WSimF.on-ev step
  with qq .FSim.fwd .WSimF.on-ev (▷-ev-elim B P₁ step)
... | Y , wQ , sim = Y , □-wev-R P₂ Q₂ (wev-τ*-pre runQ wQ) , sim

-------------------------------------------------------------------------------------
-- THE THREE RECORDS.  S1's `stab` is the only non-vacuous one: `□-stable-elim` gives a
-- SINGLE leaf (both operands stable — a `□` with a terminated operand always has a τ),
-- each spec operand settles by its own `FSim.stab` after paying its debt, the two
-- settle runs interleave with `□-τ*-settle` (legitimate: each lift leaves the other
-- operand untouched, and neither settle target is a `ret`), and the offer inclusions
-- recombine with `□-offer-mono`.  S2/S3 have `stab` VACUOUS by `▷-unstable`.
-------------------------------------------------------------------------------------

□-fsim-run P₂ Q₂ runP runQ pp qq .FSim.fwd = f-sim-□-run P₂ Q₂ runP runQ pp qq
□-fsim-run {P₁ = P₁} {Q₁ = Q₁} P₂ Q₂ runP runQ pp qq .FSim.stab st
  with □-stable-elim P₁ Q₁ st
... | stP₁ , stQ₁ with pp .FSim.stab stP₁ | qq .FSim.stab stQ₁
...   | P₂* , rP , stP* , inclP | Q₂* , rQ , stQ* , inclQ =
        (P₂* □ Q₂*)
      , □-τ*-settle P₂ Q₂ (τ*-trans runP rP) stP* (τ*-trans runQ rQ) stQ*
      , stable-□ {P = P₂*} {Q = Q₂*} stP* stQ*
      , □-offer-mono P₁ P₂* Q₁ Q₂* stP₁ stQ₁ inclP inclQ
□-fsim-run P₂ Q₂ runP runQ pp qq .FSim.div→ d = □-run-div→ P₂ Q₂ runP runQ pp qq d

▷□-fsim-L P₂ Q₂ eqQ₁ runP runQ pp qq .FSim.fwd = f-sim-▷□-L P₂ Q₂ eqQ₁ runP runQ pp qq
-- `isStable (A ▷ Q₁)` is absurd: the `▷`-node always carries its timeout τ
▷□-fsim-L {A = A} {Q₁ = Q₁} P₂ Q₂ eqQ₁ runP runQ pp qq .FSim.stab st =
  ⊥-elim (▷-unstable A Q₁ st)
▷□-fsim-L P₂ Q₂ eqQ₁ runP runQ pp qq .FSim.div→ d = ▷□-L-div→ P₂ Q₂ eqQ₁ runP pp d

▷□-fsim-R P₂ Q₂ eqP₁ runP runQ pp qq .FSim.fwd = f-sim-▷□-R P₂ Q₂ eqP₁ runP runQ pp qq
-- mirror: `isStable (B ▷ P₁)` is absurd
▷□-fsim-R {P₁ = P₁} {B = B} P₂ Q₂ eqP₁ runP runQ pp qq .FSim.stab st =
  ⊥-elim (▷-unstable B P₁ st)
▷□-fsim-R P₂ Q₂ eqP₁ runP runQ pp qq .FSim.div→ d = ▷□-R-div→ P₂ Q₂ eqP₁ runQ qq d

-------------------------------------------------------------------------------------
-- THE CONGRUENCE.  The invariant starts with NO debt on either side.
-------------------------------------------------------------------------------------

-- HEADLINE: external choice is an FSim congruence in BOTH operands, with NO side
-- condition (contrast `Par-fsim`, which needs `Sep`, and `▷`, which has no two-sided
-- congruence at all)
□-fsim : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
       → FSim R P₁ P₂ → FSim R Q₁ Q₂ → FSim R (P₁ □ Q₁) (P₂ □ Q₂)
□-fsim {P₂ = P₂} {Q₂ = Q₂} pp qq = □-fsim-run P₂ Q₂ τ*-refl τ*-refl pp qq

-------------------------------------------------------------------------------------
-- REPLICATED FOLDS.  `□⋆` / `□Fin` are plain right folds of `_□_` over `Stop`, and
-- `□-fsim` carries no side condition, so — unlike `⦀Fin-fsim` / `⦀⋆-fsim`, which must
-- thread pairwise disjointness through the fold — these are one line each: structural
-- recursion on the list / index, `fsim-refl Stop` at the empty fold.
-------------------------------------------------------------------------------------

-- replicated external choice over a `Fin`-indexed family is an FSim congruence
□Fin-fsim : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ (n : ℕ)
            (f g : Fin n → PTree E (ExtI E) R)
          → (∀ i → FSim R (f i) (g i)) → FSim R (□Fin n f) (□Fin n g)
□Fin-fsim zero    f g sim = fsim-refl Stop
□Fin-fsim (suc n) f g sim =
  □-fsim (sim fzero) (□Fin-fsim n (λ i → f (fsuc i)) (λ i → g (fsuc i)) (λ i → sim (fsuc i)))

-- replicated external choice over a LIST is an FSim congruence, pointwise
□⋆-fsim : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ (Ps Qs : List (PTree E (ExtI E) R))
        → Pointwise (FSim R) Ps Qs → FSim R (□⋆ Ps) (□⋆ Qs)
□⋆-fsim []       []       []ᵖ         = fsim-refl Stop
□⋆-fsim (P ∷ Ps) (Q ∷ Qs) (hd ∷ᵖ tl) = □-fsim hd (□⋆-fsim Ps Qs tl)

-------------------------------------------------------------------------------------
-- RETIRED `⊑FD` COROLLARY.  The shape-3 `FSim → ⊑FD` cash-out `□-mono-⊑FD` used to live
-- here.  It was a one-liner (`fsim→⊑FD (□-fsim pp qq)`) that CASHED OUT the simulation
-- witness irrecoverably (`⊑FD → FSim` completeness is out of scope) and so could never
-- consume a `⊑FD` fact; the canonical `-mono-⊑FD` name now belongs to the FACT-SHAPED
-- (`⊑FD → ⊑FD`) precongruence in `CSP.Laws.FD.ExtChoiceMonoFD`, which also carries the
-- fact-shaped replicated folds `□Fin-mono-⊑FD` / `□⋆-mono-⊑FD`.  Please do not re-add it —
-- write the one-liner at the call site, or feed it to the fact-shaped law.  Inside a
-- composite refinement keep the `FSim` and compose with `□-fsim` / `Par-fsim` /
-- `Hide-fsim` instead.
-------------------------------------------------------------------------------------
