{-# OPTIONS --guardedness #-}

-- FAILURE-SIMULATION congruence for ITERATION and the LOOPS built on it.
--
--   Iter-bind-fsim : IterDivSplit k₁ → (∀ a → FSim (A ⊎ R) (k₁ a) (k₂ a))
--                  → FSim (A ⊎ R) t₁ t₂ → FSim R (iter-bind t₁ k₁) (iter-bind t₂ k₂)
-- and, with the König hypothesis DISCHARGED (`iter-div-split`), five side-condition-free
-- corollaries:
--   iter-fsim   : (∀ a → FSim (A ⊎ R) (k₁ a) (k₂ a)) → ∀ a → FSim R (iter k₁ a) (iter k₂ a)
--   loop-fsim   : (∀ a → FSim A (body₁ a) (body₂ a)) → ∀ a → FSim R (loop body₁ a) (loop body₂ a)
--   loop0-fsim  : FSim ⊤ body₁ body₂ → FSim R (loop0 body₁) (loop0 body₂)
--   loopc-fsim  : FSim ⊤ body₁ body₂ → FSim R (loopc body₁) (loopc body₂)
--                 (`loopc` IS `loop0` by definition, so `loopc-fsim = loop0-fsim`)
--   while-fsim  : (∀ a → FSim A (body₁ a) (body₂ a))
--               → ∀ a → FSim A (while cond body₁ a) (while cond body₂ a)
--
-- ORIENTATION: in `FSim R t₁ t₂` the FIRST argument is the IMPLEMENTATION and the SECOND
-- the SPECIFICATION (`fsim→⊑FD : FSim R Q P → P ⊑FD Q`), so this says: if the spec body
-- failure-simulates the impl body at every loop state, then the spec loop failure-simulates
-- the impl loop.  Composed with `fsim→⊑FD` it is a coinductive route to
-- `loop0 body₂ ⊑FD loop0 body₁`.
--
-- The combinator is the repo's own `iter` / `iter-bind` (`CSP.Operators`), whose loop-back is
-- a `sil`-GUARDED τ:
--     force (iter-bind t k) = sil (iter k a′)            when force t ≡ ret (inj₁ a′)
--                           = ret r                       when force t ≡ ret (inj₂ r)
--                           = sil (iter-bind c k)         when force t ≡ sil c
--                           = react (iterV …) (iterT …)   when force t ≡ react v τc
-- and `loop` / `loop0` / `loopc` / `while` are `iter` at a PURE continuation
-- (`λ a′ → Ret (inj₁ a′)` resp. the `cond`-tagged variant) — which is why the statements
-- below are proved once for `iter-bind` and then instantiated through `bindκ-fsim`, the
-- pure-continuation bind congruence written for exactly this purpose.
--
-- The three fields.
--
--   fwd  : the `bwd`-free half of `CSP.Laws.Bisim.IterCong`'s `iter-bind-sim`, with
--          `≈-reaches-ret` replaced by `fsim-reaches-ret` and the residual `iter-bind-cong`
--          by `Iter-bind-fsim`.  Case analysis is on `force t₁`; every force/branch/threading
--          lemma (`fIter-r1`/`fIter-r2`/`fIter-sil`/`fIter-react`, `iterV-elim`/`iterT-elim`,
--          `iter-bind-τ`/`iter-bind-ev`/`iter-bind-τ*`, `iter-loop-τ`, `iter-stop-√`) is
--          REUSED from `IterCong` — nothing about the operator is reproved here.  At the
--          LOOP-BACK (`force t₁ ≡ ret (inj₁ a′)`) the impl takes the guard τ into
--          `iter k₁ a′`; the spec answers with `fsim-reaches-ret`'s silent run to its own
--          `ret (inj₁ a′)` state, lifted by `iter-bind-τ*`, plus that state's own loop-back
--          τ, and the residual is `Iter-bind-fsim … (kk a′)` — the corecursive knot, sitting
--          under the `WSimF` Σ-result exactly as in `iter-bind-sim`.
--
--   stab : STRICTLY SIMPLER than the bind case, and with NO side condition, because an
--          iterate state IS STABLE ONLY INSIDE THE BODY.  Of the four forces above, three
--          are non-stable outright (`sil` at the loop-back, `sil` at a body τ, `ret` at
--          termination), so `iter-stable-elim` shows `isStable (iter-bind t₁ k₁)` forces
--          `isStable t₁` — there is NO handover leaf to consider (contrast
--          `BindCong.Bind-stable-normal`, which has one).  The spec's body then settles by
--          `pp .FSim.stab`, the settling run lifts by `iter-bind-τ*`, and
--          `iter-stable-intro` re-stabilises.  Offers transfer body-wise: the composite's
--          offers live in `Event√ R` and the body's in `Event√ (A ⊎ R)`, and the body's `√`
--          is CONSUMED by the iterate (it becomes the loop-back τ or the terminal tick), so
--          the two agree exactly on the carrier-independent `evl` events — enough, because a
--          `√` offer needs a `ret` force and both sides are stable
--          (`Iter-offer-elim-stable` / `Iter-offer-intro-evl` / `Iter-offer-mono`).
--
--   div→ : the delicate field, as expected: a loop that iterates forever without visible
--          events IS a divergence, and the impl's τ-chain may cross arbitrarily many
--          loop-backs.  Deciding whether it stays inside the CURRENT iteration or completes
--          it is the ITERATE KÖNIG STEP, taken here as the explicit hypothesis
--          `IterDivSplit k₁` (a closed statement quantified over the iteration source, with
--          `k₁` fixed, so it threads through the corecursion unchanged).  `fwd` and `stab`
--          never mention it.
--
--          IT IS THEN DISCHARGED FOR EVERY `k` (`iter-div-split`), so all five corollaries
--          are unconditional.  The discharge uses NO NEW POSTULATE: it reuses the same two
--          pre-existing `dne`-certified postulates that `CSP.Laws.FSim.HideCong.div→` leans
--          on, in the same combination —
--            • `Diverges-LEM` (`CSP.Laws.FD.FDTransfer`, Derivation 10) decides whether the
--              iteration source `t` itself τ-diverges; if it does, that IS the first
--              disjunct;
--            • otherwise `¬DivModA→MAcc` (`CSP.Laws.FD.HideDivergence`, Derivation 9)
--              instantiated at the EMPTY hidden set (where a `ModAStep` is just a τ,
--              `modA∅→diverges`) turns `¬ Diverges t` into τ-ACCESSIBILITY `MAcc ∅ES t`,
--              along which `iter-div-search` walks the composite's τ-chain by well-founded
--              recursion.  Each τ of `iter-bind t k` is, by the new constructive
--              `iter-τ-elim`, EITHER a τ of `t` (one accessibility step) OR the loop-back
--              itself — and since `t` is not divergent the walk must terminate at a
--              loop-back, which is the second disjunct.
--          The repo's own iterate König postulate `CSP.Laws.FD.IterateFD.loop-Diverges→` is
--          deliberately NOT used: it is stated only for `loopStep body` at `A = ⊤`, whereas
--          `iter-div-split` covers every `k` and every state type, and needs no postulate of
--          its own.
--
--          GUARDEDNESS — the reusable lesson of this module.  The naive `div→`
--            div-prepend-τ* run (Iter-bind-fsim … .FSim.div→ dk)
--          is REJECTED: the corecursive call sits under the ordinary function
--          `div-prepend-τ*`, not under a constructor, which is the same non-constructor-
--          guarded helper chain that sank the earlier `Tail-Sim-Y` attempt at
--          `loop0-mono-⊑FD`.  The fix (the `HideCong.Round` idiom): package ONE PRODUCTIVE
--          ROUND of the spec-side divergence as data — a possibly-empty τ*-run followed by
--          AT LEAST ONE τ step, landing in an `IterDivGoal` — and let the corecursive
--          `iter-fsim-div-run` walk that run under the `Diverges.rest` COPATTERN before
--          re-entering the round generator.  Every cycle then passes through a coinductive
--          field, and `iter-fsim-round` itself is an ordinary (non-corecursive) function.
--          The `IterDivGoal` datatype is what lets the two very different outcomes of the
--          König split — "the spec already diverges outright" and "the spec is one loop-back
--          away from the next iteration" — be handed to the same corecursion.
--
-- This module declares NO postulate, no NON_TERMINATING, no sized type and no hole.
-- `Iter-bind-fsim` is classical-ingredient-free (the König step is its hypothesis); the five
-- corollaries use exactly the two pre-existing certified postulates named above.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Function using (case_of_)

open import Process_Trees

module CSP.Laws.FSim.LoopCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS        {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.Refusals   {E = E} {I = ExtI E} using (Offers)
open import Semantics.Stability  {E = E} {I = ExtI E} using (stable-not-sil; stable-not-ret)
open import Semantics.DRBisim    {E = E} {I = ExtI E} using (Diverges)
open import Semantics.FailureSim {E = E} {I = ExtI E}
  using (FSim; fsim-refl; fsim-τ*-sim)
open import CSP.Laws.Bisim.IterCong E-≟
  using ( ret-no-τ; sil-no-ev; sil-τ-inv; react-τ-inv
        ; fIter-r1; fIter-r2; fIter-sil; fIter-react
        ; iterV-elim; iterT-elim
        ; iter-bind-τ; iter-bind-ev; iter-bind-τ*; iter-loop-τ; iter-stop-√ )
open import CSP.Laws.FSim.BindCong E-≟ using (fsim-reaches-ret; bindκ-fsim)
open import CSP.Laws.FD.ParallelRefusals E-≟ using (stable→react; mk-stable)
open import CSP.Laws.Bisim.DRCongruence E-≟ using (ModAStep; maτ; maE; DivModA)
open import CSP.Laws.FD.HideDivergence E-≟ using (MAcc; macc; ¬DivModA→MAcc)
open import CSP.Laws.FD.FDTransfer E-≟ using (Diverges-LEM)

private
  variable
    ℓr ℓs : Level
    A : Set ℓ
    R : Set ℓr
    S : Set ℓs

-------------------------------------------------------------------------------------
-- WHEN IS `iter-bind t k` STABLE?  Read off its four forces: the loop-back is a `sil`, a
-- body τ is a `sil`, termination is a `ret` — none stable — so the ONLY stable iterate
-- state is one sitting at a stable `react` of the body.  There is no handover leaf.
-------------------------------------------------------------------------------------

-- `iterT` is `nothing` wherever the underlying `viewT` is (τ-branch-map intro)
iterT-nothing : (k : A → PTree E (ExtI E) (A ⊎ R)) (nt : NodeKind E (ExtI E) (A ⊎ R))
                {i : AnyTypes (ExtI E)} {a : proj₁ i}
              → viewT nt i a ≡ nothing → iterT k nt i a ≡ nothing
iterT-nothing k nt {i} {a} eq with viewT nt i a
... | nothing = refl
... | just _  = case eq of λ ()

-- …and only there (τ-branch-map elim)
iterT-nothing-inv : (k : A → PTree E (ExtI E) (A ⊎ R)) (nt : NodeKind E (ExtI E) (A ⊎ R))
                    {i : AnyTypes (ExtI E)} {a : proj₁ i}
                  → iterT k nt i a ≡ nothing → viewT nt i a ≡ nothing
iterT-nothing-inv k nt {i} {a} eq with viewT nt i a
... | nothing = refl
... | just _  = case eq of λ ()

-- a stable composite with a `react` body forces that body's τ-branch map to be everywhere
-- `nothing` — i.e. the body is itself stable
iter-stable-τc : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
                 {v  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) (A ⊎ R)))}
                 {τc : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) (A ⊎ R)))}
               → PTree.force t ≡ react v τc → isStable (iter-bind t k)
               → ∀ i a → τc i a ≡ nothing
iter-stable-τc t k {v} {τc} eqt st i a with stable→react {t = iter-bind t k} st
... | v′ , τc′ , eqI , h =
      iterT-nothing-inv k (react v τc)
        (subst (λ g → g i a ≡ nothing)
               (sym (proj₂ (react-injective (trans (sym (fIter-react k t eqt)) eqI))))
               (h i a))

-- STABILITY ELIM: a stable iterate state is a stable body state.  The case analysis is on a
-- NAMED node argument with its force-equation supplied (never `with PTree.force t in eqt`):
-- `isStable (iter-bind t k)` only computes once `force t` is concrete, and a `with` would
-- abstract the wrong occurrences.
iter-stable-elim-node : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
                        (nt : NodeKind E (ExtI E) (A ⊎ R))
                      → PTree.force t ≡ nt → isStable (iter-bind t k) → isStable t
iter-stable-elim-node t k (ret (inj₁ a′)) eqt st =
  ⊥-elim (stable-not-sil {t = iter-bind t k} st (fIter-r1 k t eqt))
iter-stable-elim-node t k (ret (inj₂ r))  eqt st =
  ⊥-elim (stable-not-ret {t = iter-bind t k} st (fIter-r2 k t eqt))
iter-stable-elim-node t k (sil c)         eqt st =
  ⊥-elim (stable-not-sil {t = iter-bind t k} st (fIter-sil k t eqt))
iter-stable-elim-node t k (react v τc)    eqt st =
  mk-stable {t = t} eqt (iter-stable-τc t k eqt st)

-- the elimination at the body's actual node
iter-stable-elim : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
                 → isStable (iter-bind t k) → isStable t
iter-stable-elim t k st = iter-stable-elim-node t k (PTree.force t) refl st

-- STABILITY INTRO: a stable body state makes the iterate state stable (`iterT` inherits
-- "everywhere nothing" from the body's own τ-branch map)
iter-stable-intro : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
                  → isStable t → isStable (iter-bind t k)
iter-stable-intro t k st with stable→react {t = t} st
... | v , τc , eqt , h =
      mk-stable {t = iter-bind t k} (fIter-react k t eqt)
                (λ i a → iterT-nothing k (react v τc) (h i a))

-------------------------------------------------------------------------------------
-- OFFER DECOMPOSITION for `stab`.  THE √ ASYMMETRY IS VISIBLE IN THE TYPES: the iterate's
-- offers live in `Event√ R`, the body's in `Event√ (A ⊎ R)`, and the iterate CONSUMES the
-- body's `√` (it becomes the loop-back τ at `inj₁` and the terminal tick at `inj₂`).  So the
-- two offer sets can only ever agree on the carrier-independent `evl` events — which is
-- enough, because with a stable body a `√` offer is impossible on either side.
-------------------------------------------------------------------------------------

-- OFFER ELIM: every offer of an iterate state with a `react` body is an `evl` offer of the
-- body (a composite `√` would need a `ret` force, which a `react` body does not give)
Iter-offer-elim-react : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
                        {v  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) (A ⊎ R)))}
                        {τc : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) (A ⊎ R)))}
                      → PTree.force t ≡ react v τc
                      → ∀ (e : Event√ R) → Offers (iter-bind t k) e
                      → Σ[ l ∈ Event ] ((e ≡ evl l) × Offers t (evl l))
Iter-offer-elim-react t k eqt e (_ , sRet eqf) =
  ⊥-elim (case trans (sym (fIter-react k t eqt)) eqf of λ ())
Iter-offer-elim-react t k {v} {τc} eqt e (_ , sVis {at = at} {a = a} eqf br)
  with iterV-elim k (react v τc)
         (subst (λ g → g at a ≡ just _)
                (sym (proj₁ (react-injective (trans (sym (fIter-react k t eqt)) eqf))))
                br)
... | t″ , vv , refl =
      evLabel (proj₁ at) (proj₂ at) a , refl , (t″ , sVis eqt vv)

-- the same for a STABLE body (a stable state forces to a `react` node)
Iter-offer-elim-stable : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
                       → isStable t
                       → ∀ (e : Event√ R) → Offers (iter-bind t k) e
                       → Σ[ l ∈ Event ] ((e ≡ evl l) × Offers t (evl l))
Iter-offer-elim-stable t k st e off with stable→react {t = t} st
... | _ , _ , eqt , _ = Iter-offer-elim-react t k eqt e off

-- OFFER INTRO: an `evl` offer of the body is an offer of the iterate state (unconditional —
-- the body's `√` is the one offer that does NOT survive, and `evl` excludes it)
Iter-offer-intro-evl : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
                     → ∀ (l : Event) → Offers t (evl l) → Offers (iter-bind t k) (evl l)
Iter-offer-intro-evl t k l (t′ , sVis eqf br) = iter-bind t′ k , iter-bind-ev k t (sVis eqf br)

-- OFFER MONOTONICITY: body-wise offer inclusion composes to iterate-wise offer inclusion
Iter-offer-mono : (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
                  (t₁ t₂ : PTree E (ExtI E) (A ⊎ R))
                → isStable t₂
                → (∀ (e : Event√ (A ⊎ R)) → Offers t₂ e → Offers t₁ e)
                → ∀ (e : Event√ R) → Offers (iter-bind t₂ k₂) e → Offers (iter-bind t₁ k₁) e
Iter-offer-mono k₁ k₂ t₁ t₂ st₂ incl e off
  with Iter-offer-elim-stable t₂ k₂ st₂ e off
... | l , refl , o = Iter-offer-intro-evl t₁ k₁ l (incl (evl l) o)

-------------------------------------------------------------------------------------
-- THE `stab` FIELD.  One leaf only, and NO side condition.
-------------------------------------------------------------------------------------

-- a stable impl iterate state is stable IN ITS BODY; settle the spec's body with its own
-- `FSim.stab`, lift that silent run through the iterate, and compose the offer inclusions
iter-fsim-stab : (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
                 {t₁ t₂ : PTree E (ExtI E) (A ⊎ R)}
               → FSim (A ⊎ R) t₁ t₂ → isStable (iter-bind t₁ k₁)
               → Σ[ M ∈ PTree E (ExtI E) R ]
                   ( (iter-bind t₂ k₂) ─[τ*]─► M × isStable M
                   × (∀ (e : Event√ R) → Offers M e → Offers (iter-bind t₁ k₁) e) )
iter-fsim-stab k₁ k₂ {t₁} {t₂} pp st with pp .FSim.stab (iter-stable-elim t₁ k₁ st)
... | t₂* , run , st* , incl =
      iter-bind t₂* k₂
    , iter-bind-τ* k₂ run
    , iter-stable-intro t₂* k₂ st*
    , Iter-offer-mono k₁ k₂ t₁ t₂* st* incl

-------------------------------------------------------------------------------------
-- THE `div→` FIELD, part 1: the ITERATE KÖNIG STEP.
-------------------------------------------------------------------------------------

-- The iterate König step for a FIXED continuation: an infinite τ-chain of `iter-bind t k`
-- either stays inside the current iteration `t` forever, or that iteration completes (`t`
-- silently reaches a `ret (inj₁ a′)` loop-back state) and the NEXT iterate `iter k a′`
-- diverges.  Stated as a hypothesis (`Iter-bind-fsim` takes it), and discharged for every
-- `k` below by `iter-div-split`.
IterDivSplit : ∀ {ℓr′} {A′ : Set ℓ} {R′ : Set ℓr′}
             → (k : A′ → PTree E (ExtI E) (A′ ⊎ R′)) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr′)
IterDivSplit {A′ = A′} {R′ = R′} k =
    ∀ (t : PTree E (ExtI E) (A′ ⊎ R′))
  → Diverges (iter-bind t k)
  → Diverges t
  ⊎ (Σ[ tᵣ ∈ PTree E (ExtI E) (A′ ⊎ R′) ] Σ[ a′ ∈ A′ ]
       ( (t ─[τ*]─► tᵣ) × (PTree.force tᵣ ≡ ret (inj₁ a′)) × Diverges (iter k a′) ))

-- τ-INVERSION for the iterate: every τ of `iter-bind t k` is EITHER a τ of the body (target
-- still in iterate form) OR the loop-back guard at a `ret (inj₁ a′)` body state.  This is
-- the whole content of "the τ-chain can only leave the iteration through a loop-back", and
-- it is fully constructive.  (Node argument + force-equation, not `with PTree.force t`, so
-- the `force t ≡ ret (inj₁ a′)` in the conclusion is not abstracted away.)
iter-τ-elim-node : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
                   (nt : NodeKind E (ExtI E) (A ⊎ R)) → PTree.force t ≡ nt
                 → {u : PTree E (ExtI E) R} → (iter-bind t k) ─[ τ ]─► u
                 → (Σ[ t′ ∈ PTree E (ExtI E) (A ⊎ R) ] ((t ─[ τ ]─► t′) × (u ≡ iter-bind t′ k)))
                 ⊎ (Σ[ a′ ∈ A ] ((PTree.force t ≡ ret (inj₁ a′)) × (u ≡ iter k a′)))
iter-τ-elim-node t k (ret (inj₁ a′)) eqt step =
  inj₂ (a′ , eqt , sil-τ-inv (fIter-r1 k t eqt) step)
iter-τ-elim-node t k (ret (inj₂ r))  eqt step =
  ⊥-elim (ret-no-τ (fIter-r2 k t eqt) step)
iter-τ-elim-node t k (sil c)         eqt step =
  inj₁ (c , sSil eqt , sil-τ-inv (fIter-sil k t eqt) step)
iter-τ-elim-node t k (react v τc)    eqt step
  with react-τ-inv (fIter-react k t eqt) step
... | i , a , br with iterT-elim k (react v τc) br
...   | t′ , vτ , teq = inj₁ (t′ , sTau eqt vτ , teq)

-- the inversion at the body's actual node
iter-τ-elim : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
            → {u : PTree E (ExtI E) R} → (iter-bind t k) ─[ τ ]─► u
            → (Σ[ t′ ∈ PTree E (ExtI E) (A ⊎ R) ] ((t ─[ τ ]─► t′) × (u ≡ iter-bind t′ k)))
            ⊎ (Σ[ a′ ∈ A ] ((PTree.force t ≡ ret (inj₁ a′)) × (u ≡ iter k a′)))
iter-τ-elim t k step = iter-τ-elim-node t k (PTree.force t) refl step

-- at the EMPTY hidden set a `ModAStep` can only be a τ (nothing is a member of `∅ES`).  A
-- four-line local copy of `CSP.Laws.FSim.HideCong`'s pair of the same name: importing
-- HideCong for them would drag the whole hiding stack into a loop law.
modA∅-step : {t t′ : PTree E (ExtI E) S} → ModAStep ∅ES t t′ → t ─[ τ ]─► t′
modA∅-step (maτ s)     = s
modA∅-step (maE mem _) = ⊥-elim mem

-- …hence an `∅ES`-modulo divergence is a plain τ-divergence, which is what lets the
-- certified `¬DivModA→MAcc` be instantiated at `∅ES` to obtain τ-ACCESSIBILITY
modA∅→diverges : {t : PTree E (ExtI E) S} → DivModA ∅ES t → Diverges t
modA∅→diverges dm .Diverges.next = dm .DivModA.maNext
modA∅→diverges dm .Diverges.step = modA∅-step (dm .DivModA.maStep)
modA∅→diverges dm .Diverges.rest = modA∅→diverges (dm .DivModA.maRest)

-- THE SEARCH.  With a NON-divergent body state `t`, walk the composite's τ-chain along `t`'s
-- τ-accessibility: `iter-τ-elim` makes each τ either a body τ (consuming one accessibility
-- step) or the loop-back — and the latter must be reached, since the accessibility recursion
-- is well-founded.  Split into two forward-declared halves so the `Diverges` fields of the
-- chain are read off as ordinary arguments (`u` a pattern variable, so the `u ≡ …` equations
-- of `iter-τ-elim` can be matched by `refl`).
iter-div-search : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
                → MAcc ∅ES t → Diverges (iter-bind t k)
                → Σ[ tᵣ ∈ PTree E (ExtI E) (A ⊎ R) ] Σ[ a′ ∈ A ]
                    ( (t ─[τ*]─► tᵣ) × (PTree.force tᵣ ≡ ret (inj₁ a′)) × Diverges (iter k a′) )
iter-div-search-step : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
                     → MAcc ∅ES t → (u : PTree E (ExtI E) R)
                     → (iter-bind t k) ─[ τ ]─► u → Diverges u
                     → Σ[ tᵣ ∈ PTree E (ExtI E) (A ⊎ R) ] Σ[ a′ ∈ A ]
                         ( (t ─[τ*]─► tᵣ) × (PTree.force tᵣ ≡ ret (inj₁ a′)) × Diverges (iter k a′) )

iter-div-search t k acc d =
  iter-div-search-step t k acc _ (d .Diverges.step) (d .Diverges.rest)

iter-div-search-step t k (macc rs) u st du with iter-τ-elim t k st
-- the loop-back: this iteration is over, and what is left of the chain diverges the next one
... | inj₂ (a′ , eqr , refl) = t , a′ , τ*-refl , eqr , du
-- a body τ: one accessibility step consumed, keep walking
... | inj₁ (t′ , stτ , refl) with iter-div-search t′ k (rs (maτ stτ)) du
...   | tᵣ , a′ , run , eqr , dl = tᵣ , a′ , τ*-step stτ run , eqr , dl

-- THE DISCHARGE, for EVERY continuation: `Diverges-LEM` decides whether the current
-- iteration's source diverges; if not, `¬DivModA→MAcc ∅ES` turns that into τ-accessibility
-- and the search finds the loop-back.  Both postulates are pre-existing and certified from
-- the single `dne` of `CSP.Laws.ClassicalFromLEM`; no new postulate is introduced.
iter-div-split : (k : A → PTree E (ExtI E) (A ⊎ R)) → IterDivSplit k
iter-div-split k t d with Diverges-LEM t
... | inj₁ dt = inj₁ dt
... | inj₂ nd =
      inj₂ (iter-div-search t k
             (¬DivModA→MAcc ∅ES (λ dm → nd (modA∅→diverges dm))) d)

-- a divergence of the body lifts to a divergence of the iterate (each body τ threads through
-- `iter-bind-τ`; corecursion guarded under the `Diverges` fields)
Diverges-iter : (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
              → Diverges t → Diverges (iter-bind t k)
Diverges-iter t k d .Diverges.next = iter-bind (d .Diverges.next) k
Diverges-iter t k d .Diverges.step = iter-bind-τ k t (d .Diverges.step)
Diverges-iter t k d .Diverges.rest = Diverges-iter (d .Diverges.next) k (d .Diverges.rest)

-------------------------------------------------------------------------------------
-- THE `div→` FIELD, part 2: the PRODUCTIVE transfer.
--
-- The operands and the two hypotheses are module parameters here, because the search state
-- (`IterDivGoal`) is a DATATYPE indexed by spec trees and must mention them.
-------------------------------------------------------------------------------------

module _ {ℓr′} {A′ : Set ℓ} {R′ : Set ℓr′}
         (k₁ k₂ : A′ → PTree E (ExtI E) (A′ ⊎ R′))
         (kön : IterDivSplit k₁)
         (kk  : ∀ a → FSim (A′ ⊎ R′) (k₁ a) (k₂ a)) where

  -- WHERE THE SPEC-SIDE DIVERGENCE SEARCH CAN STAND: either the spec state already diverges
  -- outright (the body-livelock outcome — nothing left to decide), or it is `iter-bind t₂ k₂`
  -- for an operand pair whose IMPL iterate diverges (the loop-back outcome — the state the
  -- transfer re-enters at every completed iteration).  Having both as constructors of ONE
  -- datatype is what lets a single corecursion serve both arms of the König split.
  data IterDivGoal : PTree E (ExtI E) R′ → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr′) where
    div-now   : {T : PTree E (ExtI E) R′} → Diverges T → IterDivGoal T
    div-later : {t₁ t₂ : PTree E (ExtI E) (A′ ⊎ R′)}
              → FSim (A′ ⊎ R′) t₁ t₂ → Diverges (iter-bind t₁ k₁)
              → IterDivGoal (iter-bind t₂ k₂)

  -- ONE PRODUCTIVE ROUND of the spec's τ-divergence: a possibly-EMPTY τ*-run followed by AT
  -- LEAST ONE τ step, landing in a state where the search can stand again.  Holding that
  -- last step separately is exactly what makes the corecursion below productive (the
  -- `CSP.Laws.FSim.HideCong.Round` idiom).
  record Round (T : PTree E (ExtI E) R′) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr′) where
    field
      {rMid} : PTree E (ExtI E) R′       -- spec state after the round's τ*-run
      {rNxt} : PTree E (ExtI E) R′       -- spec state after the round's final τ
      rRun   : T ─[τ*]─► rMid
      rStep  : rMid ─[ τ ]─► rNxt
      rGoal  : IterDivGoal rNxt
  open Round

  -- THE ROUND GENERATOR — an ORDINARY function, no corecursion.  `div-now` peels one step
  -- off the ready-made divergence.  `div-later` consults the König split: a body livelock is
  -- transferred by the operand's own `div→` and lifted by `Diverges-iter` (the round ends in
  -- `div-now`); a COMPLETED iteration lifts both silent spec runs with `iter-bind-τ*`, takes
  -- the spec's own loop-back guard as the round's final τ (`iter-loop-τ`), and re-enters
  -- `div-later` at the next iteration's operand pair.
  iter-fsim-round : {T : PTree E (ExtI E) R′} → IterDivGoal T → Round T
  iter-fsim-round (div-now d) = record
    { rRun  = τ*-refl
    ; rStep = d .Diverges.step
    ; rGoal = div-now (d .Diverges.rest) }
  iter-fsim-round (div-later {t₁} {t₂} pp d) with kön t₁ d
  ... | inj₁ dt₁ with pp .FSim.div→ dt₁
  ...   | dt₂ = record
          { rRun  = τ*-refl
          ; rStep = iter-bind-τ k₂ t₂ (dt₂ .Diverges.step)
          ; rGoal = div-now (Diverges-iter (dt₂ .Diverges.next) k₂ (dt₂ .Diverges.rest)) }
  iter-fsim-round (div-later {t₁} {t₂} pp d) | inj₂ (tᵣ , a′ , run , eqr , dk)
    with fsim-τ*-sim run pp
  ... | t₂′ , run₂ , rel with fsim-reaches-ret rel eqr
  ...   | p₂ , run₃ , eqr₂ = record
          { rRun  = iter-bind-τ* k₂ (τ*-trans run₂ run₃)
          ; rStep = iter-loop-τ k₂ p₂ eqr₂
          ; rGoal = div-later (kk a′) dk }

  -- THE CORECURSION.  Walk the round's leading τ*-run under the `Diverges.rest` COPATTERN and
  -- only then call the round generator again: every cycle passes through a coinductive field,
  -- so this is productive.  (Prepending the run with an ordinary helper — `div-prepend-τ*`
  -- applied to a corecursive result — is what the guardedness checker rejects.)
  iter-fsim-div-run : {T M N : PTree E (ExtI E) R′}
                    → T ─[τ*]─► M → M ─[ τ ]─► N → IterDivGoal N → Diverges T
  iter-fsim-div-run {N = N} τ*-refl st g .Diverges.next = N
  iter-fsim-div-run          τ*-refl st g .Diverges.step = st
  iter-fsim-div-run          τ*-refl st g .Diverges.rest =
    iter-fsim-div-run (iter-fsim-round g .rRun) (iter-fsim-round g .rStep)
                      (iter-fsim-round g .rGoal)
  iter-fsim-div-run (τ*-step {t′ = mid} s rest) st g .Diverges.next = mid
  iter-fsim-div-run (τ*-step             s rest) st g .Diverges.step = s
  iter-fsim-div-run (τ*-step             s rest) st g .Diverges.rest =
    iter-fsim-div-run rest st g

  -- the `div→` field itself: start the search at the impl's diverging iterate
  iter-fsim-div→ : {t₁ t₂ : PTree E (ExtI E) (A′ ⊎ R′)}
                 → FSim (A′ ⊎ R′) t₁ t₂
                 → Diverges (iter-bind t₁ k₁) → Diverges (iter-bind t₂ k₂)
  iter-fsim-div→ pp d with iter-fsim-round (div-later pp d)
  ... | r = iter-fsim-div-run (r .rRun) (r .rStep) (r .rGoal)

-------------------------------------------------------------------------------------
-- THE CONGRUENCE.  Forward declarations (no old-style mutual block): the corecursive
-- `Iter-bind-fsim` residuals sit under the `WSimF` Σ-results of `f-sim-Iter`, exactly the
-- guardedness discipline of `CSP.Laws.Bisim.IterCong.iter-bind-sim`.  Only the BODY state is
-- ever forced (`with PTree.force t₁`) — never a composite.
-------------------------------------------------------------------------------------

-- HEADLINE: `iter-bind` is an FSim congruence (the spec's body failure-simulates the impl's
-- body at every loop state and at the current iteration), modulo the iterate König step for
-- the impl continuation
Iter-bind-fsim : (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
               → IterDivSplit k₁ → (∀ a → FSim (A ⊎ R) (k₁ a) (k₂ a))
               → {t₁ t₂ : PTree E (ExtI E) (A ⊎ R)} → FSim (A ⊎ R) t₁ t₂
               → FSim R (iter-bind t₁ k₁) (iter-bind t₂ k₂)

-- the forward-simulation half: invert an impl iterate step by cases on `force t₁`
f-sim-Iter : (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
           → IterDivSplit k₁ → (∀ a → FSim (A ⊎ R) (k₁ a) (k₂ a))
           → {t₁ t₂ : PTree E (ExtI E) (A ⊎ R)} → FSim (A ⊎ R) t₁ t₂
           → WSimF (FSim R) (iter-bind t₁ k₁) (iter-bind t₂ k₂)

-- τ steps
f-sim-Iter k₁ k₂ kön kk {t₁} {t₂} pp .WSimF.on-tau step with PTree.force t₁ in eqt
-- a terminated iteration offers no τ
... | ret (inj₂ r) = ⊥-elim (ret-no-τ (fIter-r2 k₁ t₁ eqt) step)
-- THE LOOP-BACK: the spec silently follows its body to its own `ret (inj₁ a′)` and then takes
-- its own loop-back guard; the residual is the congruence at the next iteration's operands
... | ret (inj₁ a′) with sil-τ-inv (fIter-r1 k₁ t₁ eqt) step | fsim-reaches-ret pp eqt
...   | refl | p₂ , run₂ , eqr₂ =
        iter k₂ a′
      , wτ (τ*-trans (iter-bind-τ* k₂ run₂) (τ*-step (iter-loop-τ k₂ p₂ eqr₂) τ*-refl))
      , Iter-bind-fsim k₁ k₂ kön kk (kk a′)
-- a silent step of the body
f-sim-Iter k₁ k₂ kön kk {t₁} {t₂} pp .WSimF.on-tau step | sil c
  with sil-τ-inv (fIter-sil k₁ t₁ eqt) step | pp .FSim.fwd .WSimF.on-tau (sSil eqt)
...   | refl | c₂ , wτ run , relc =
        iter-bind c₂ k₂ , wτ (iter-bind-τ* k₂ run) , Iter-bind-fsim k₁ k₂ kön kk relc
-- an internal (τ-branch) step of the body
f-sim-Iter k₁ k₂ kön kk {t₁} {t₂} pp .WSimF.on-tau step | react v τc
  with react-τ-inv (fIter-react k₁ t₁ eqt) step
...   | i , a , br with iterT-elim k₁ (react v τc) br
...     | t″ , vτ , refl with pp .FSim.fwd .WSimF.on-tau (sTau eqt vτ)
...       | t₂″ , wτ run , rel =
            iter-bind t₂″ k₂ , wτ (iter-bind-τ* k₂ run) , Iter-bind-fsim k₁ k₂ kön kk rel

-- visible steps (including the iterate's own √ at `inj₂`)
f-sim-Iter k₁ k₂ kön kk {t₁} {t₂} pp .WSimF.on-ev step with PTree.force t₁ in eqt
-- the loop-back and a body τ are silent: nothing visible there
... | ret (inj₁ a′) = ⊥-elim (sil-no-ev (fIter-r1 k₁ t₁ eqt) step)
... | sil c         = ⊥-elim (sil-no-ev (fIter-sil k₁ t₁ eqt) step)
-- TERMINATION: the impl ticks `√ r`; the spec silently reaches its own `ret (inj₂ r)` and
-- ticks the same value
... | ret (inj₂ r) with step
...   | sRet eqf with trans (sym (fIter-r2 k₁ t₁ eqt)) eqf | fsim-reaches-ret pp eqt
...     | refl | p₂ , run₂ , eqr₂ =
          deadlock
        , wev (iter-bind-τ* k₂ run₂) (iter-stop-√ k₂ p₂ eqr₂) τ*-refl
        , fsim-refl deadlock
f-sim-Iter k₁ k₂ kön kk {t₁} {t₂} pp .WSimF.on-ev step | ret (inj₂ r) | sVis eqf _ =
  ⊥-elim (case trans (sym (fIter-r2 k₁ t₁ eqt)) eqf of λ ())
-- a visible offer of the body (a √ is impossible: `force (iter-bind t₁ k₁)` is a `react`)
f-sim-Iter k₁ k₂ kön kk {t₁} {t₂} pp .WSimF.on-ev step | react v τc with step
...   | sRet eqf = ⊥-elim (case trans (sym (fIter-react k₁ t₁ eqt)) eqf of λ ())
...   | sVis {at = at} {a = a} eqf br
        with iterV-elim k₁ (react v τc)
               (subst (λ g → g at a ≡ just _)
                      (sym (proj₁ (react-injective
                                    (trans (sym (fIter-react k₁ t₁ eqt)) eqf))))
                      br)
...     | t″ , vv , refl with pp .FSim.fwd .WSimF.on-ev (sVis eqt vv)
...       | t₂″ , wev pre evst post , rel =
            iter-bind t₂″ k₂
          , wev (iter-bind-τ* k₂ pre) (iter-bind-ev k₂ _ evst) (iter-bind-τ* k₂ post)
          , Iter-bind-fsim k₁ k₂ kön kk rel

Iter-bind-fsim k₁ k₂ kön kk pp .FSim.fwd     = f-sim-Iter     k₁ k₂ kön kk pp
Iter-bind-fsim k₁ k₂ kön kk pp .FSim.stab st = iter-fsim-stab k₁ k₂ pp st
Iter-bind-fsim k₁ k₂ kön kk pp .FSim.div→ d  = iter-fsim-div→ k₁ k₂ kön kk pp d

-------------------------------------------------------------------------------------
-- THE COROLLARIES.  All five are side-condition-free: `iter-div-split` discharges the König
-- hypothesis for every continuation.
-------------------------------------------------------------------------------------

-- ITERATION is an FSim congruence
iter-fsim : (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
          → (∀ a → FSim (A ⊎ R) (k₁ a) (k₂ a))
          → ∀ a → FSim R (iter k₁ a) (iter k₂ a)
iter-fsim k₁ k₂ kk a = Iter-bind-fsim k₁ k₂ (iter-div-split k₁) kk (kk a)

-- the STATEFUL FOREVER LOOP is an FSim congruence.  `loop body a` is `iter` at the PURE
-- continuation `λ a′ → Ret (inj₁ a′)`, so the body hypothesis is lifted to a loop-step
-- hypothesis by `bindκ-fsim` (the pure-continuation bind congruence).
loop-fsim : (body₁ body₂ : A → PTree E (ExtI E) A)
          → (∀ a → FSim A (body₁ a) (body₂ a))
          → ∀ a → FSim R (loop {R = R} body₁ a) (loop {R = R} body₂ a)
loop-fsim {R = R} body₁ body₂ bb a =
  iter-fsim (λ a″ → body₁ a″ >>= λ a′ → Ret (inj₁ a′))
            (λ a″ → body₂ a″ >>= λ a′ → Ret (inj₁ a′))
            (λ a″ → bindκ-fsim (λ a′ → Ret (inj₁ a′)) (λ a′ → Ret (inj₁ a′))
                               (λ r → inj₁ r , refl) (λ r → fsim-refl _) (bb a″))
            a

-- the NON-STATEFUL forever loop is an FSim congruence
loop0-fsim : {body₁ body₂ : PTree E (ExtI E) (⊤ {ℓ})}
           → FSim (⊤ {ℓ}) body₁ body₂ → FSim R (loop0 {R = R} body₁) (loop0 {R = R} body₂)
loop0-fsim {body₁ = body₁} {body₂ = body₂} bb =
  loop-fsim (λ _ → body₁) (λ _ → body₂) (λ _ → bb) tt

-- `loopc` is `loop0` by definition, so it inherits the congruence
loopc-fsim : {body₁ body₂ : PTree E (ExtI E) (⊤ {ℓ})}
           → FSim (⊤ {ℓ}) body₁ body₂ → FSim R (loopc {R = R} body₁) (loopc {R = R} body₂)
loopc-fsim bb = loop0-fsim bb

-- the CONDITIONAL loop is an FSim congruence (same route, with the `cond`-tagged pure
-- continuation `λ a′ → Ret (if cond a′ then inj₁ a′ else inj₂ a′)`)
while-fsim : (cond : A → Bool) (body₁ body₂ : A → PTree E (ExtI E) A)
           → (∀ a → FSim A (body₁ a) (body₂ a))
           → ∀ a → FSim A (while cond body₁ a) (while cond body₂ a)
while-fsim cond body₁ body₂ bb a =
  iter-fsim (λ a″ → body₁ a″ >>= λ a′ → Ret (if cond a′ then inj₁ a′ else inj₂ a′))
            (λ a″ → body₂ a″ >>= λ a′ → Ret (if cond a′ then inj₁ a′ else inj₂ a′))
            (λ a″ → bindκ-fsim (λ a′ → Ret (if cond a′ then inj₁ a′ else inj₂ a′))
                               (λ a′ → Ret (if cond a′ then inj₁ a′ else inj₂ a′))
                               (λ r → (if cond r then inj₁ r else inj₂ r) , refl)
                               (λ r → fsim-refl _) (bb a″))
            a
