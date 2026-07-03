{-# OPTIONS --guardedness #-}

------------------------------------------------------------
-- Imports
------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List using () renaming (drop to dropᴸ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Process_Trees
open PTree

module Semantics.LTL.Refinement {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Semantics.LTS                {ℓ}{ℓe}{ℓi}{E}{I}
open import Semantics.WeakBisim          {ℓ}{ℓe}{ℓi}{E}{I}
  using (_═[_]═►_; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures           {ℓ}{ℓe}{ℓi}{E}{I}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_; τ*-then; weaken-ev)
open import Semantics.LTL.Traces_Based   {ℓ}{ℓe}{ℓi}{E}{I}

------------------------------------------------------------
-- §1 Trace-observable frame predicates
--
-- A FramePred `P` is *trace-observable* iff its truth at a frame is
-- determined solely by the visible part exposed in a CSP trace word:
--
--   • on a `step t e` frame it factors through the event `e` alone
--     (it ignores the residual process `t`), via an underlying event
--     predicate `Q : Event√ R → Set ℓa` with `P (step t e) ≡ Q e`; and
--   • on every terminator frame (`done`/`stuck`/`div`) it is uninhabited
--     (a finite trace word records no terminator, so a trace-observable
--     atom is false there).
--
-- ENCODING CHOICE.  We expose `Q` *and* a propositional equality
-- `P (step t e) ≡ Q e` (rather than a dedicated `evAtom` former, or a
-- semantic biconditional).  Rationale for the downstream bridge (Task 7):
--   – Task 3's finite-word evaluator reads the head event as `Q e`; the
--     `≡` lets `subst`/`trans` transport the OPERATIONAL `P (step t e)`
--     to the WORD reading `Q e` and back, in both bridge directions.
--   – The terminator clauses are stated as `P … → Lift ℓa ⊥` (the
--     predicate is empty) rather than `P … ≡ Lift ℓa ⊥`.  This is the key
--     to admitting the VM atoms: `atCoin`/`atDrink` return the *bare*
--     `⊥` (level lzero), and `⊥` is NOT propositionally equal to
--     `Lift lzero ⊥` (record vs. data), so an equality form would reject
--     them; `⊥ → Lift ℓa ⊥` is trivially `λ ()`.
--   – Because `atCoin`'s defining lambda matches only on the `Event√`
--     part of a `step` frame and discards the PTree, `P (step t e) ≡ Q e`
--     holds *definitionally* (`refl`) — so the Task-10 witnesses are
--     `Q , refl , (λ ()) , (λ ()) , (λ ())`.
------------------------------------------------------------

TraceObs : ∀ {ℓr} {R : Set ℓr} {ℓa}
         → FramePred ℓa R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓa)
TraceObs {ℓr} {R} {ℓa} P =
  Σ[ Q ∈ (Event√ R → Set ℓa) ]
    ( (∀ {t e} → P (step t e) ≡ Q e)
    × (∀ {t r} → P (done t r)  → Lift ℓa ⊥)
    × (∀ {t}   → P (stuck t)     → Lift ℓa ⊥)
    × (∀ {t}   → P (Frame.div t) → Lift ℓa ⊥) )

------------------------------------------------------------
-- §2 The Safety LTL-formula class (M1 constructors)
--
-- Closed under: ⊤', trace-observable atoms, ¬, ∧, X, and F.  All other
-- M1 operators are DERIVED:
--   _∨_  = ¬(¬φ ∧ ¬ψ)        ⇒ s-∨ from s-¬/s-∧
--   _⇒_  = (¬φ) ∨ ψ          ⇒ s-⇒ from s-∨/s-¬
--   G_ φ = ¬ (F (¬ φ))       ⇒ s-G from s-¬/s-F
-- so that `Safety (G (atCoin ⇒ X atDrink))` is derivable WITHOUT a bare
-- `_U_` constructor.  `s-F` (= `Safety (⊤' U φ)`) is the only `U`-shaped
-- entry admitted at M1; the general `s-U` is deferred to M2 (Task 11).
------------------------------------------------------------

data Safety {ℓr} {R : Set ℓr} {ℓa}
          : LTLᵗ ℓa R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓa) where
  s-⊤'   : Safety ⊤'
  s-atom : ∀ {P}   → TraceObs P → Safety (atom P)
  s-¬    : ∀ {φ}   → Safety φ → Safety (¬ φ)
  s-∧    : ∀ {φ ψ} → Safety φ → Safety ψ → Safety (φ ∧ ψ)
  s-X    : ∀ {φ}   → Safety φ → Safety (X φ)
  s-F    : ∀ {φ}   → Safety φ → Safety (F φ)

-- Derived closure combinators (∨ / ⇒ / G), matching the LTLᵗ definitions.
s-∨ : ∀ {ℓr} {R : Set ℓr} {ℓa} {φ ψ : LTLᵗ ℓa R}
    → Safety φ → Safety ψ → Safety (φ ∨ ψ)
s-∨ sφ sψ = s-¬ (s-∧ (s-¬ sφ) (s-¬ sψ))

s-⇒ : ∀ {ℓr} {R : Set ℓr} {ℓa} {φ ψ : LTLᵗ ℓa R}
    → Safety φ → Safety ψ → Safety (φ ⇒ ψ)
s-⇒ sφ sψ = s-∨ (s-¬ sφ) sψ

s-G : ∀ {ℓr} {R : Set ℓr} {ℓa} {φ : LTLᵗ ℓa R}
    → Safety φ → Safety (G φ)
s-G sφ = s-¬ (s-F (s-¬ sφ))

------------------------------------------------------------
-- §3 Finite-word LTL evaluator `⟦_⟧ᵀ`
--
-- Evaluate an LTLᵗ formula over a finite event WORD `s : List (Event√ R)`
-- (a CSP trace).  A word position `i` corresponds to the `i`-th event in
-- `s`; the formula is read at position 0 (the head of `s`), with `X`/`U`
-- shifting along the word by `drop`.
--
-- WORD-END CONVENTIONS (consumed by the Task-7 soundness bridge):
--
--   • `atom P` reads the HEAD step-event of the word.  At end-of-word
--     (`[]`) there is no step frame, so the atom is `Lift ℓa ⊥` (false).
--     On `e ∷ s` it is `P (step deadlock e)`: we feed the canonical
--     `deadlock` PTree into the unused STATE slot of the frame.  This is
--     SOUND because `TraceObs P` guarantees `P (step t e) ≡ Q e` is
--     INDEPENDENT of the state `t`, so the fabricated state is invisible.
--     We choose the dummy-PTree form (option i) over threading the
--     `TraceObs` witness (option ii) so that `⟦_⟧ᵀ` is TOTAL on every
--     `LTLᵗ` value, not only on `Safety` ones — `_⊨ᵀ_` then needs no
--     side-condition, and Task 7 transports `P (step t e) ≡ P (step
--     deadlock e) ≡ Q e` purely by the witness's state-independence.
--
--   • `X φ` at end-of-word (`[]`) is VACUOUSLY TRUE (`Lift ℓa ⊤`).  A
--     finite word has no successor position past its end, so a "next"
--     obligation is discharged trivially there.  This convention is what
--     makes the Task-7 bridge for `G (atCoin ⇒ X atDrink)` go through:
--     `G` quantifies over every suffix INCLUDING `[]`, and at `[]` the
--     guard `atCoin` is already false (its head-atom is `Lift ℓa ⊥`), so
--     the implication is vacuous regardless; choosing `X φ ⟦⟧ᵀ [] = ⊤`
--     keeps the obligation discharged on the empty-suffix arm too.
--
--   • `φ U ψ` is the natural finite-word Until: there is an index `n`
--     with `ψ` holding on the `n`-suffix and `φ` on every strictly
--     earlier suffix.  This is the CORRECT semantics (not a stub): `F`
--     (= `⊤' U_`) and `G` (= `¬ (F (¬ ·))`) are defined through it and
--     are used in M1, so the clause must be right.
------------------------------------------------------------

⟦_⟧ᵀ : ∀ {ℓr} {R : Set ℓr} {ℓa} → LTLᵗ ℓa R → List (Event√ R) → Set ℓa
⟦_⟧ᵀ {ℓa = ℓa} ⊤'        s        = Lift ℓa ⊤
⟦_⟧ᵀ {ℓa = ℓa} (atom P)  []       = Lift ℓa ⊥
⟦_⟧ᵀ           (atom P)  (e ∷ s)  = P (step deadlock e)
⟦_⟧ᵀ {ℓa = ℓa} (¬ φ)     s        = ⟦ φ ⟧ᵀ s → Lift ℓa ⊥
⟦_⟧ᵀ           (φ ∧ ψ)   s        = ⟦ φ ⟧ᵀ s × ⟦ ψ ⟧ᵀ s
⟦_⟧ᵀ {ℓa = ℓa} (X φ)     []       = Lift ℓa ⊤
⟦_⟧ᵀ           (X φ)     (e ∷ s)  = ⟦ φ ⟧ᵀ s
⟦_⟧ᵀ           (φ U ψ)   s        =
  Σ[ n ∈ ℕ ] ( ⟦ ψ ⟧ᵀ (dropᴸ n s)
             × (∀ m → m < n → ⟦ φ ⟧ᵀ (dropᴸ m s)) )

------------------------------------------------------------
-- §4 Trace-based satisfaction `_⊨ᵀ_`
--
-- `t ⊨ᵀ φ` :  every CSP trace word `s` of `t` satisfies `φ` read at the
-- word's head.  For a safety property `G ψ` this unfolds (via `¬`/`F`/`U`)
-- to "ψ holds at every position of every trace of `t`" (see report's
-- `⟦ G (atom P) ⟧ᵀ` sanity check).  Because a Q-trace is a P-trace under
-- `⊑T`, `P ⊨ᵀ φ` directly discharges `Q ⊨ᵀ φ`'s obligation.
--
-- SOUNDNESS SCOPE (certified, see VendingMachine_LTL_Sat's "Negative
-- result" section for the machine-checked counterexample).  `_⊨ᵀ_` is
-- sound for X-FREE (state-invariant) safety formulas, but NOT for
-- "next"-time (`X_`) formulas: CSP traces (`traces`/`_⟹⟨_⟩_`) are
-- PREFIX-CLOSED, so a word can stop right after the event an `atom`
-- guard fires on, before any successor event is observed.  `⟦_⟧ᵀ` then
-- reads `X φ` past the end of that (nonempty) word as `⟦ φ ⟧ᵀ [] = Lift
-- ⊥` (false), even though the *operational*, coinductive `Trace` always
-- has a genuine next frame (terminators stutter) and the analogous `_⊨_`
-- formula can hold there. Concretely, `VM_body_impl ⊨ᵀ
-- (G (atCoin ⇒ X atDrink))` is REFUTABLE via the one-letter trace
-- `coin ∷ []`, while `VM_body_impl ⊨ (G (atCoin ⇒ X atDrink))` is
-- PROVABLE (`vm-safety`) — see
-- `CSP.Examples.VendingMachine.VendingMachine_LTL_Sat`'s
-- `vm-⊨ᵀ-safety-impossible`.
--
-- This is NOT a bug in `⊑T-transfer-ᵀ` below: that lemma is a purely
-- monotone transfer (`P ⊑T Q → P ⊨ᵀ φ → Q ⊨ᵀ φ`) and is sound for
-- whatever `φ` `_⊨ᵀ_` itself supports. The limitation is specifically
-- that `_⊨ᵀ_` (the finite, prefix-closed-word reading) does not coincide
-- with the operational `_⊨_` for X-using `φ` — i.e. trace refinement
-- `⊑T` is too coarse to transfer next-time LTL; bisimulation (`∼`/
-- `≈DR`) is the appropriate refinement notion for that purpose.
------------------------------------------------------------

_⊨ᵀ_ : ∀ {ℓr} {R : Set ℓr} {ℓa}
     → PTree E I R → LTLᵗ ℓa R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓa)
t ⊨ᵀ φ = ∀ {s} → traces t s → ⟦ φ ⟧ᵀ s

------------------------------------------------------------
-- §5 Unit 3a — weak-step → ⟹ bridge lemmas
--
-- These three lemmas connect the weak-step machinery from
-- Semantics.WeakBisim to the CSP big-step `_⟹⟨_⟩_` from
-- Semantics.Failures.  They are used in Task 5's soundness bridge.
------------------------------------------------------------

-- A τ*-sequence produces an empty-trace ⟹ run.
τ*→⟹ : ∀ {ℓr} {R : Set ℓr} {p q : PTree E I R}
      → p ─[τ*]─► q → p ⟹⟨ [] ⟩ q
τ*→⟹ τ*-refl        = ⟹-refl
τ*→⟹ (τ*-step s r)  = ⟹-τ s (τ*→⟹ r)

-- A single weak visible step produces a one-event-trace ⟹ run.
wev→⟹ : ∀ {ℓr} {R : Set ℓr} {p q : PTree E I R} {l : Event√ R}
       → p ═[ ev l ]═► q → p ⟹⟨ l ∷ [] ⟩ q
wev→⟹ w = weaken-ev w ⟹-refl

------------------------------------------------------------
-- §6 Unit 3b — operational `Trace` position → CSP trace (op→csp)
--
-- Read the first `n` step-events of an operational (root-indexed)
-- `Trace R t` as a CSP trace word, and prove that this word is a genuine
-- big-step `_⟹⟨_⟩_` run from `t` to the state reached after `n` steps —
-- i.e. `dropIdx n tr`.  Terminator frames (`done`/`stuck`/`div`) stutter
-- (`tail tr = tr`), so they contribute no further events and leave the
-- state fixed at `t`.
------------------------------------------------------------

-- The first `n` step-events of an operational trace.  Terminators
-- contribute none (the trace stutters there, matching `tail`'s self-loop).
eventsOf : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
         → ℕ → (Trace R) t → List (Event√ R)
eventsOf zero    tr                    = []
eventsOf (suc n) (step {e = e} _ rest) = e ∷ eventsOf n (force rest)
eventsOf (suc n) (done _)              = []
eventsOf (suc n) (stuck _)             = []
eventsOf (suc n) (div _)               = []

-- Append/transitivity for CSP big-step runs.  By definition of `_++_` the
-- empty-prefix and cons cases line up so the resulting word is `s₁ ++ s₂`.
⟹-++ : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s₁ s₂ : List (Event√ R)}
     → p ⟹⟨ s₁ ⟩ q → q ⟹⟨ s₂ ⟩ r → p ⟹⟨ s₁ ++ s₂ ⟩ r
⟹-++ ⟹-refl       g = g
⟹-++ (⟹-τ x f)    g = ⟹-τ x (⟹-++ f g)
⟹-++ (⟹-ev x f)   g = ⟹-ev x (⟹-++ f g)

-- Every operational trace position `n` yields a CSP trace from `t` to the
-- state `dropIdx n tr` reached at that position.
--
-- Index reductions relied on (from `Traces_Based`):
--   • `dropIdx zero tr = t` (definitional)            ⇒ `⟹-refl` base.
--   • `tail (step _ rest) = force rest`, hence
--     `dropIdx (suc n) (step st rest) = dropIdx n (force rest)`
--     (definitional)                                  ⇒ `⟹-++` of `wev→⟹`
--     with the recursive call; `(e ∷ []) ++ w = e ∷ w` is definitional.
--   • At terminators `tail tr = tr`, so the codomain `dropIdx (suc n) tr`
--     does not reduce to `t` definitionally; `dropIdx-stutter` gives the
--     propositional equation and we `subst` `⟹-refl` along it.
op→csp : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
       → (n : ℕ) (tr : (Trace R) t)
       → t ⟹⟨ eventsOf n tr ⟩ (dropIdx n tr)
op→csp zero    tr                     = ⟹-refl
op→csp (suc n) (step st rest)         = ⟹-++ (wev→⟹ st) (op→csp n (force rest))
op→csp (suc n) tr@(done eq)           =
  subst (_ ⟹⟨ [] ⟩_) (sym (dropIdx-stutter (suc n) tr tt)) ⟹-refl
op→csp (suc n) tr@(stuck st)          =
  subst (_ ⟹⟨ [] ⟩_) (sym (dropIdx-stutter (suc n) tr tt)) ⟹-refl
op→csp (suc n) tr@(div dv)            =
  subst (_ ⟹⟨ [] ⟩_) (sym (dropIdx-stutter (suc n) tr tt)) ⟹-refl

------------------------------------------------------------
-- §7 Trace-refinement transfer for `_⊨ᵀ_`
--
-- `⊑T-transfer-ᵀ`: trace refinement P ⊑T Q (all Q-traces are P-traces)
-- transfers `_⊨ᵀ_`: any Q-trace `q-tr` is first converted to a P-trace via
-- `P⊑Q s q-tr`, then fed to `Pᵀ : P ⊨ᵀ φ`, yielding `⟦φ⟧ᵀ s`.
------------------------------------------------------------

⊑T-transfer-ᵀ : ∀ {ℓr} {R : Set ℓr} {ℓa} {φ : LTLᵗ ℓa R} {P Q : PTree E I R}
              → P ⊑T Q → P ⊨ᵀ φ → Q ⊨ᵀ φ
⊑T-transfer-ᵀ P⊑Q Pᵀ {s} q-tr = Pᵀ (P⊑Q s q-tr)

------------------------------------------------------------
-- §8 Operational ↔ word alignment for the backward bridge (Task 7)
--
-- These bookkeeping lemmas relate the finite word read from an operational
-- trace (`eventsOf`) to the operational `drop`/`tail` navigation, so the
-- trace-side evaluator `⟦_⟧ᵀ` and the operational evaluator `⟦_⟧` can be
-- lined up event-by-event at each position.
------------------------------------------------------------

-- A terminator trace records no events: `eventsOf j` of it is empty.
eventsOf-term : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                  (j : ℕ) (tr : (Trace R) t)
                → IsTerminator (frameOf tr) → eventsOf j tr ≡ []
eventsOf-term zero    tr            term = refl
eventsOf-term (suc j) (step _ _)    ()
eventsOf-term (suc j) tr@(done _)   term = refl
eventsOf-term (suc j) tr@(stuck _)  term = refl
eventsOf-term (suc j) tr@(div _)    term = refl

-- Dropping past a terminator keeps us at a terminator: its `eventsOf` is empty.
-- (We only need the empty-word conclusion, so we phrase it directly on
--  `eventsOf` and recurse on `n`, using the stutter `tail tr = tr` at leaves.)
eventsOf-drop-term : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                       (n j : ℕ) (tr : (Trace R) t)
                     → IsTerminator (frameOf tr) → eventsOf j (drop n tr) ≡ []
eventsOf-drop-term zero    j tr term = eventsOf-term j tr term
eventsOf-drop-term (suc n) j tr@(done eq)  term = eventsOf-drop-term n j tr term
eventsOf-drop-term (suc n) j tr@(stuck st) term = eventsOf-drop-term n j tr term
eventsOf-drop-term (suc n) j tr@(div dv)   term = eventsOf-drop-term n j tr term

-- ALIGNMENT.  Dropping the first `n` word-letters of the `(n + j)`-event word
-- of `tr` is the same word as the `j`-event word read AFTER navigating `n`
-- operational steps (`drop n tr`).  Proved by induction on `n`; the terminator
-- arm uses `eventsOf-drop-term` (both sides are then `[]`).
eventsOf-drop : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                  (n j : ℕ) (tr : (Trace R) t)
                → dropᴸ n (eventsOf (n + j) tr) ≡ eventsOf j (drop n tr)
eventsOf-drop zero    j tr            = refl
eventsOf-drop (suc n) j (step st rest) = eventsOf-drop n j (force rest)
eventsOf-drop (suc n) j tr@(done eq)  =
  sym (eventsOf-drop-term (suc n) j tr tt)
eventsOf-drop (suc n) j tr@(stuck st) =
  sym (eventsOf-drop-term (suc n) j tr tt)
eventsOf-drop (suc n) j tr@(div dv)   =
  sym (eventsOf-drop-term (suc n) j tr tt)

------------------------------------------------------------
-- §9 Backward bridge `⊨ᵀ → ⊨` for the guarded-G safety shape (Task 7)
--
-- We prove the VM target shape `ψ = (atom Pc) ⇒ X (atom Pd)` with both
-- atoms trace-observable.  This covers `G (atCoin ⇒ X atDrink)` — the only
-- guarded-G property the downstream VM capstone (vT Task 9) consumes.  The
-- fully-general `Safety ψ` induction is deferred (its `_U_`/nesting cases
-- require a frame↔word evaluator bridge beyond the demo's needs).
--
-- Strategy (per the brief).  `t ⊨ (G ψ) = ∀ tr → ⟦ G ψ ⟧ tr`.  Apply the
-- CONSTRUCTIVE `⟦G⟧⁺⇒⟦G⟧`: suffices `∀ n → ⟦ ψ ⟧ (drop n tr)`.  At a
-- terminator frame the guard atom `Pc` is empty (`TraceObs`), discharging
-- the implication with no word.  At a `step` frame we feed the trace
-- hypothesis `t ⊨ᵀ (G ψ)` a length-`(n+2)` CSP word (`op→csp`); since
-- `⟦ G ψ ⟧ᵀ` is the finite-word `¬ (F (¬ ψ))`, we hand it a position-`n`
-- bad-prefix witness `⟦ F (¬ ψ) ⟧ᵀ` built from the operational premise
-- pieces (`pc`, `nXd`), transported across `TraceObs`'s state-independence
-- and the `eventsOf`/`drop` alignment, to obtain `Lift ⊥`.
------------------------------------------------------------

⊨ᵀ→⊨-G-VM : ∀ {ℓr} {R : Set ℓr} {ℓa}
              {Pc Pd : FramePred ℓa R} {t : PTree E I R}
            → TraceObs Pc → TraceObs Pd
            → t ⊨ᵀ (G ((atom Pc) ⇒ X (atom Pd)))
            → t ⊨ ((G ((atom Pc) ⇒ X (atom Pd))))
⊨ᵀ→⊨-G-VM {ℓa = ℓa} {Pc = Pc} {Pd = Pd} {t = t}
          (Qc , toPc , cDone , cStuck , cDiv) (Qd , toPd , dDone , dStuck , dDiv) ⊨ᵀGψ tr =
  ⟦G⟧⁺⇒⟦G⟧ {φ = (atom Pc) ⇒ X (atom Pd)} {tr = tr} go
  where
    ψ : LTLᵗ ℓa _
    ψ = (atom Pc) ⇒ X (atom Pd)

    -- The per-position obligation `⟦ ψ ⟧ (drop n tr)`.
    go : ∀ n → ⟦ ψ ⟧ (drop n tr)
    go n with drop n tr in eqn
    -- TERMINATOR frames: the guard `Pc` is empty, so the premise's `¬¬ Pc`
    -- component refutes itself.
    go n | done eq  = λ { (nnPc , _) → nnPc (λ pc → cDone pc) }
    go n | stuck st = λ { (nnPc , _) → nnPc (λ pc → cStuck pc) }
    go n | div dv   = λ { (nnPc , _) → nnPc (λ pc → cDiv pc) }
    -- STEP frame `step t₀ e`.  Premise `(nnPc , nXd)`:
    --   nnPc : (Pc (step t₀ e) → Lift ⊥) → Lift ⊥
    --   nXd  : Pd (frameOf (tail (drop n tr))) → Lift ⊥
    go n | step {t = t₀} {e = e} st rest =
      λ { (nnPc , nXd) → nnPc (λ pc → feedHyp pc nXd) }
      where
        -- The CSP word of length n+2 and its position-n bad prefix.
        feedHyp : Pc (step t₀ e)
                → (⟦ atom Pd ⟧ (force rest) → Lift ℓa ⊥)
                → Lift ℓa ⊥
        feedHyp pc nXd =
          ⊨ᵀGψ (dropIdx (n + 2) tr , op→csp (n + 2) tr)
               (n , badPrefix , λ _ _ → lift tt)
          where
            -- `Pc (step deadlock e)` from `pc`, via state-independence.
            pc′ : Pc (step deadlock e)
            pc′ = subst (λ X → X) (trans toPc (sym toPc)) pc

            -- `⟦ ¬ ψ ⟧ᵀ` at the word position-n suffix.  We build it on
            -- `eventsOf 2 (drop n tr)` and transport along the alignment
            -- `eventsOf-drop n 2 tr` to `dropᴸ n (eventsOf (n+2) tr)`.
            badPrefix : ⟦ ¬ ψ ⟧ᵀ (dropᴸ n (eventsOf (n + 2) tr))
            badPrefix =
              subst (λ w → ⟦ ¬ ψ ⟧ᵀ w)
                    (sym (eventsOf-drop n 2 tr))
                    (subst (λ u → ⟦ ¬ ψ ⟧ᵀ (eventsOf 2 u))
                           (sym eqn)
                           bad2)
              where
                -- The bad witness read on the concrete 2-event word of
                -- `step t₀ e …` — i.e. `e ∷ eventsOf 1 (tail (drop n tr))`.
                bad2 : ⟦ ¬ ψ ⟧ᵀ (eventsOf 2 (step st rest))
                bad2 f = f (myNNPc , myNXd)
                  where
                    -- Pc is true (trace-side) at the head event.
                    myNNPc : (⟦ atom Pc ⟧ᵀ (eventsOf 2 (step st rest)) → Lift ℓa ⊥)
                           → Lift ℓa ⊥
                    myNNPc k = k pc′
                    -- The next-drink obligation is refuted via `nXd`.
                    myNXd : ⟦ X (atom Pd) ⟧ᵀ (eventsOf 2 (step st rest)) → Lift ℓa ⊥
                    myNXd = nextRefute (force rest) nXd
                      where
                        -- `nXd : ⟦ atom Pd ⟧ (force rest) → Lift ⊥` already
                        -- refutes the operational next-frame drink.
                        -- `nextRefute` takes
                        -- the successor trace `u` together with the operational
                        -- refuter at `u`'s frame, cases on `u` to read the
                        -- word's second letter, and aligns `Pd`.
                        nextRefute : (u : (Trace _) _)
                                   → (⟦ atom Pd ⟧ u → Lift ℓa ⊥)
                                   → ⟦ atom Pd ⟧ᵀ (eventsOf 1 u) → Lift ℓa ⊥
                        nextRefute (step {e = e₁} st₁ rest₁) refute traceXd =
                          -- word = e₁ ∷ [];  ⟦atom Pd⟧ᵀ = Pd (step deadlock e₁)
                          refute (subst (λ X → X) (trans toPd (sym toPd)) traceXd)
                        nextRefute (done eq)   refute ()
                        nextRefute (stuck st₁) refute ()
                        nextRefute (div dv₁)   refute ()
