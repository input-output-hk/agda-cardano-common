{-# OPTIONS --guardedness #-}

-- The bridge ≈DR ⟹ ≈FD : divergence-respecting weak bisimulation implies
-- failures-divergences equivalence on the pure-react LTS.
--
-- The DIVERGENCES half is fully constructive (it just transports a divergence
-- along the weak simulation, using the div→/div← correspondence of DRbisim).
--
-- The FAILURES half needs ONE classical principle: a non-divergent process must
-- be able to reach a STABLE or TERMINATED (ret) state by some finite τ*-run — i.e.
-- a τ-normal-form.  (Earlier this concluded just `isStable t′`, which is UNSOUND: a
-- terminated `ret` state is non-divergent yet never stable, so it would prove ⊥.)
-- This is the only postulate in the development; it is the constructive obstruction
-- (bar induction) that makes the failures model classically flavoured.

open import Level using (Level; Lift; lift; lower; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module Semantics.DRImpliesFD
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS                 {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.WeakBisim           {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.DRBisim             {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Refusals            {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Failures            {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.FailuresDivergences {ℓ} {ℓe} {ℓi} {E} {I}
  using (IsDivergence; divergences; failures⊥; _⊑F⊥_; _⊑D_; _⊑FD_; _≈FD_)

-------------------------------------------------------------------------------------
-- Stability vs. steps.
-- A `with` on `isStable t` only reduces once `PTree.force t` is concrete, so each
-- helper splits the force AND lists `isStable t` (and the force-equality) in the
-- `with` so the predicate computes in every branch.
-------------------------------------------------------------------------------------

nothing≢just : ∀ {ℓa} {A : Set ℓa} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

-- a stable state's force cannot be `sil`
stable-not-sil : ∀ {ℓr} {R : Set ℓr} {t u : PTree E I R}
               → isStable t → PTree.force t ≡ sil u → ⊥
stable-not-sil {t = t} st eq with PTree.force t | st | eq
... | ret _    | _       | ()
... | sil _    | lift ()  | _
... | react _ _ | _       | ()

-- a stable state's force cannot be `ret` either (ret is not stable)
stable-not-ret : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} {r : R}
               → isStable t → PTree.force t ≡ ret r → ⊥
stable-not-ret {t = t} st eq with PTree.force t | st | eq
... | ret _    | lift ()  | _
... | sil _    | _        | ()
... | react _ _ | _        | ()

-- a stable state's τ-branch continuation is everywhere `nothing`
stable-react-τc : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                 {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))}
                 {τc : (i  : AnyTypes I) → ContinueType i  (Maybe (PTree E I R))}
               → isStable t → PTree.force t ≡ react v τc
               → ∀ (i : AnyTypes I) (a : proj₁ i) → τc i a ≡ nothing
stable-react-τc {t = t} st eq with PTree.force t | st | eq
... | ret _     | _    | ()
... | sil _     | _    | ()
... | react _ _  | stf  | refl = stf

-- hence a stable state performs no τ-step at all
stable-no-τ : ∀ {ℓr} {R : Set ℓr} {t u : PTree E I R}
            → isStable t → t ─[ τ ]─► u → ⊥
stable-no-τ {t = t} st (sSil eq) = stable-not-sil {t = t} st eq
stable-no-τ {t = t} st (sTau {τc = τc} {i = i} {a = a} eq br) =
  nothing≢just (trans (sym (stable-react-τc {t = t} st eq i a)) br)

-- … so a stable state cannot diverge …
stable→¬div : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
            → isStable t → ¬ Diverges t
stable→¬div st d = stable-no-τ st (d .Diverges.step)

-- … and a τ*-run out of a stable state is necessarily empty
stable→τ*-refl : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R}
               → isStable t → t ─[τ*]─► t′ → t′ ≡ t
stable→τ*-refl st τ*-refl        = refl
stable→τ*-refl st (τ*-step s _)  = ⊥-elim (stable-no-τ st s)

-------------------------------------------------------------------------------------
-- THE one classical postulate: convergence yields a reachable τ-normal-form,
-- i.e. a state that is stable OR terminated (ret).  (Concluding `isStable t′` alone
-- is false — `Ret tt` is a non-divergent counterexample with no stable derivative.)
-------------------------------------------------------------------------------------

postulate
  ¬-divergent→normal : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                     → ¬ Diverges t
                     → Σ[ t′ ∈ PTree E I R ]
                         (t ─[τ*]─► t′ × (isStable t′ ⊎ Σ[ r ∈ R ] (PTree.force t′ ≡ ret r)))

-------------------------------------------------------------------------------------
-- DRbisim simulates τ-abstracting big-steps (the DRbisim analogue of `trace-sim`).
-------------------------------------------------------------------------------------

dr-trace-sim : ∀ {ℓr} {R : Set ℓr} {P Q P′ : PTree E I R} {s}
             → DRbisim R P Q → P ⟹⟨ s ⟩ P′
             → Σ[ Q′ ∈ PTree E I R ] (Q ⟹⟨ s ⟩ Q′ × DRbisim R P′ Q′)
dr-trace-sim pq ⟹-refl = _ , ⟹-refl , pq
dr-trace-sim pq (⟹-τ pτ rest) with pq .DRbisim.fwd .WSimF.on-tau pτ
... | _ , qτ , p₁q₁ with dr-trace-sim p₁q₁ rest
...   | Q′ , q⟹ , p′q′ = Q′ , weaken-τ qτ q⟹ , p′q′
dr-trace-sim pq (⟹-ev pev rest) with pq .DRbisim.fwd .WSimF.on-ev pev
... | _ , qev , p₁q₁ with dr-trace-sim p₁q₁ rest
...   | Q′ , q⟹ , p′q′ = Q′ , weaken-ev qev q⟹ , p′q′

-- appending a (silent) τ*-run to the end of a big-step keeps the same trace
⟹-then-τ* : ∀ {ℓr} {R : Set ℓr} {P Q Q′ : PTree E I R} {s}
           → P ⟹⟨ s ⟩ Q → Q ─[τ*]─► Q′ → P ⟹⟨ s ⟩ Q′
⟹-then-τ* ⟹-refl         tτ = τ*-then tτ ⟹-refl
⟹-then-τ* (⟹-τ pτ rest)   tτ = ⟹-τ pτ (⟹-then-τ* rest tτ)
⟹-then-τ* (⟹-ev pev rest) tτ = ⟹-ev pev (⟹-then-τ* rest tτ)

-------------------------------------------------------------------------------------
-- Stable-state absorption: a stable Q stays DR-bisimilar across P's silent moves
-- and preserves P's offers.  (Both use that Q, being stable, matches a τ-move only
-- by staying put — `stable→τ*-refl`.)
-------------------------------------------------------------------------------------

dr-absorb-τ* : ∀ {ℓr} {R : Set ℓr} {Q P P′ : PTree E I R}
             → isStable Q → DRbisim R Q P → P ─[τ*]─► P′ → DRbisim R Q P′
dr-absorb-τ* stQ qp τ*-refl          = qp
dr-absorb-τ* stQ qp (τ*-step pτ rest) with qp .DRbisim.bwd .WSimF.on-tau pτ
... | Q₁ , wτ q→q₁ , p₁q₁ with stable→τ*-refl stQ q→q₁
...   | refl = dr-absorb-τ* stQ (drbisim-sym p₁q₁) rest

offers-preserved : ∀ {ℓr} {R : Set ℓr} {Q P : PTree E I R} {e : Event√ R}
                 → isStable Q → DRbisim R Q P → Offers P e → Offers Q e
offers-preserved stQ qp (P′ , pev) with qp .DRbisim.bwd .WSimF.on-ev pev
... | Q′ , wev q→qa qaev qb→q′ , _ with stable→τ*-refl stQ q→qa
...   | refl = _ , qaev

-- a stable state cannot be DR-bisimilar to a terminated (ret) state: the ret offers
-- √, but a stable (react) state offers no √, so simulating that √-step forces `force Q`
-- to be `ret`, contradicting stability.
stable-≉-ret : ∀ {ℓr} {R : Set ℓr} {Q P : PTree E I R} {r : R}
             → isStable Q → DRbisim R Q P → PTree.force P ≡ ret r → ⊥
stable-≉-ret {Q = Q} {P = P} stQ qp eqP with qp .DRbisim.bwd .WSimF.on-ev (sRet {p = P} eqP)
... | _ , wev q→qa qaev qb→q′ , _ with stable→τ*-refl stQ q→qa
...   | refl with qaev
...     | sRet eqQ = stable-not-ret {t = Q} stQ eqQ

-------------------------------------------------------------------------------------
-- The bridge.
-------------------------------------------------------------------------------------

-- divergences are respected (constructive): transport along the simulation + div→
drbisim→⊑D : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → DRbisim R P Q → P ⊑D Q
drbisim→⊑D pq d with dr-trace-sim (drbisim-sym pq) (d .IsDivergence.reach)
... | Pw , p⟹ , qwpw = record
        { prefix  = d .IsDivergence.prefix
        ; suffix  = d .IsDivergence.suffix
        ; split   = d .IsDivergence.split
        ; witness = Pw
        ; reach   = p⟹
        ; divwit  = qwpw .DRbisim.div→ (d .IsDivergence.divwit)
        }

-- divergence-strict failures are respected (failures via the postulate)
drbisim→⊑F⊥ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → DRbisim R P Q → P ⊑F⊥ Q
drbisim→⊑F⊥ pq (inj₂ dQ) = inj₂ (drbisim→⊑D pq dQ)
drbisim→⊑F⊥ pq (inj₁ (Qw , q⟹ , stQw , norefuse))
  with dr-trace-sim (drbisim-sym pq) q⟹
... | Pw , p⟹ , qwpw
      with ¬-divergent→normal (λ dPw → stable→¬div stQw (qwpw .DRbisim.div← dPw))
...     | Pw′ , pw→pw′ , inj₁ stPw′ =
          inj₁ (Pw′ , ⟹-then-τ* p⟹ pw→pw′ , stPw′ ,
                λ e Be off → norefuse e Be
                  (offers-preserved stQw (dr-absorb-τ* stQw qwpw pw→pw′) off))
...     | Pw′ , pw→pw′ , inj₂ (r , eqret) =
          ⊥-elim (stable-≉-ret stQw (dr-absorb-τ* stQw qwpw pw→pw′) eqret)

drbisim→⊑FD : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → DRbisim R P Q → P ⊑FD Q
drbisim→⊑FD pq = drbisim→⊑F⊥ pq , drbisim→⊑D pq

drbisim→≈FD : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → DRbisim R P Q → P ≈FD Q
drbisim→≈FD pq = drbisim→⊑FD pq , drbisim→⊑FD (drbisim-sym pq)
