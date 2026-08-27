{-# OPTIONS --guardedness #-}

-- INTERFACE-PARALLEL / INTERLEAVING INTERCHANGE, via STRONG BISIMULATION:
--
--   Interchange : (P₁ ⦀ P₂) ∥⇘ A ⇙ (Q₁ ⦀ Q₂)  ∼  (P₁ ∥⇘ A ⇙ Q₁) ⦀ (P₂ ∥⇘ A ⇙ Q₂)
--
-- i.e. an interface parallel over two interleavings may be REGROUPED component-wise.
-- Lifted to `≈DR` / `≈FD` at the bottom of the module.
--
-- SIDE CONDITION (`ICond`, the weakest this proof needs).  With value-level
-- per-component alphabets `α₁ α₂ : Alpha`:
--
--   (1) `OffersOnly αᵢ Pᵢ` and `OffersOnly αᵢ Qᵢ`, and `Disj α₁ α₂`
--       — component 1 and component 2 share NO event.  Without it the left may
--       synchronise `P₁` with `Q₂` across components, a pairing the right does not
--       have.  This half is NECESSARY, and refuting it is MACHINE-CHECKED:
--       `CSP.Laws.FD.ParallelInterchangeCounterexample.interchange-no-Disj` exhibits
--       processes satisfying (2) but not (1) where the left performs an event the
--       right cannot perform at all — so the two differ already on the length-one
--       trace ⟨h⟩, not merely as bisimulations.
--   (2) `Sep A P₁ Q₁` and `Sep A P₂ Q₂` — within a component, the two families never
--       both offer the same OUTSIDE-`A` event.  Without it `Par` builds its inline
--       both-offer overlap node `(P′∥Q) ⊓ (P∥Q′)`, and the two sides commit that
--       overlap at different times: on the left the overlap wraps the whole composite
--       (so nothing else is offered until it resolves), on the right it wraps only
--       component 1 and the OTHER component keeps offering across it.  The `evBoth`
--       cases of the proof below are exactly where this bites.
--
--       STATUS of (2): it is required by THIS proof, and the obstruction is the same
--       one already recorded for parallel ASSOCIATIVITY — cf. the header of
--       `CSP.Laws.FD.ParallelAssoc`, which states that `(P∥Q)∥R` vs `P∥(Q∥R)` is
--       proved FD-DIRECT and is "NOT a weak/strong bisim" precisely because "when
--       P,Q,R all offer the same outside-`A` event, the two bracketings commit their
--       overlaps in a different order".  It is NOT, however, backed by a
--       machine-checked counterexample here: whether the interchange law survives at
--       `⊑FD`/`≈FD` without (2) — as associativity does — is OPEN.
--
-- Both `∅ES`-side obligations that would otherwise be needed (`P₁` vs `P₂` and `Q₁`
-- vs `Q₂` never both-offer) come for free from `Disj`, so they are NOT extra fields.
--
-- STRUCTURE.  A single strong bisimulation, forward and backward halves written out
-- separately because the two sides have different shapes.  Every case is a two-level
-- decomposition — `Par-τ-elim` / `Par-ev-elim` at the outer operator, then again at
-- the inner one — followed by re-assembly with the intro lemmas `Par-τ-L`/`Par-τ-R`,
-- `Par-sync`, `Par-soloL`/`Par-soloR`.  The non-offer hypotheses that `Par-soloL/R`
-- demand are produced by `noOffer` from a "this tree cannot step on that event"
-- proof, which is what `Disj` (across components) and `Sep` (within one) supply.
--
-- The four `ICond` updaters `icP₁`/`icP₂`/`icQ₁`/`icQ₂` carry the invariant along a
-- step of the corresponding component.
--
-- ZERO postulates, no NON_TERMINATING, no sized types, no holes.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.ParallelInterchange {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.DRBisim {E = E} {I = ExtI E}
  using (_≈DR_; drbisim-refl; drbisim-trans)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Traces.TraceLawsParallel E-≟
  using (Mg; Par-τ-L; Par-τ-R; Par-sync; Par-soloL; Par-soloR)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (ParτR; τL; τR; Par-τ-elim
        ; ParevR; evSync; evL; evR; evBoth; ev√; Par-ev-elim
        ; Par-force-ret-inv; fPar-rr)
open import CSP.Laws.Bisim.DRCongruence    E-≟ using (Sep; cong-⦀)
open import CSP.Laws.Bisim.DRCongruenceRep E-≟
  using (Alpha; Disj; OffersOnly; OffersOnly-Par; unionAlpha; OffersOnly-⦀Fin⁺
        ; sep-from-OffersOnly)

private
  variable
    ℓr : Level

  -- the symmetric ⊤-merge carried by `Par⊤` / `∥⇘_⇙` / `⦀`
  tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
  tm _ _ = tt

-------------------------------------------------------------------------------------
-- The side condition
-------------------------------------------------------------------------------------

-- `ICond α₁ α₂ A P₁ P₂ Q₁ Q₂`: the two families are confined to per-component
-- alphabets (`α₁` for component 1, `α₂` for component 2) and, within each component,
-- the P-side and the Q-side never both offer an outside-`A` event.  Alphabet
-- DISJOINTNESS is a separate parameter of the law (it does not change along steps,
-- and neither do the alphabets, so only these six witnesses need updating).
record ICond (α₁ α₂ : Alpha) (A : EventSet)
             (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr}))
     : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  field
    ooP₁ : OffersOnly α₁ P₁
    ooP₂ : OffersOnly α₂ P₂
    ooQ₁ : OffersOnly α₁ Q₁
    ooQ₂ : OffersOnly α₂ Q₂
    sepP : Sep A P₁ Q₁
    sepQ : Sep A P₂ Q₂
open ICond

-- carry the invariant along a step of P₁ (its alphabet witness advances, and the
-- component-1 `Sep` advances on its LEFT operand)
icP₁ : ∀ {α₁ α₂ A} {P₁ P₂ Q₁ Q₂ P₁′ : PTree E (ExtI E) (⊤ {ℓr})} {l}
     → P₁ ─[ l ]─► P₁′ → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂ → ICond α₁ α₂ A P₁′ P₂ Q₁ Q₂
icP₁ st ic = record { ooP₁ = OffersOnly.step (ic .ooP₁) st ; ooP₂ = ic .ooP₂
                    ; ooQ₁ = ic .ooQ₁ ; ooQ₂ = ic .ooQ₂
                    ; sepP = Sep.stepL (ic .sepP) st ; sepQ = ic .sepQ }

-- ... along a step of P₂
icP₂ : ∀ {α₁ α₂ A} {P₁ P₂ Q₁ Q₂ P₂′ : PTree E (ExtI E) (⊤ {ℓr})} {l}
     → P₂ ─[ l ]─► P₂′ → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂ → ICond α₁ α₂ A P₁ P₂′ Q₁ Q₂
icP₂ st ic = record { ooP₁ = ic .ooP₁ ; ooP₂ = OffersOnly.step (ic .ooP₂) st
                    ; ooQ₁ = ic .ooQ₁ ; ooQ₂ = ic .ooQ₂
                    ; sepP = ic .sepP ; sepQ = Sep.stepL (ic .sepQ) st }

-- ... along a step of Q₁
icQ₁ : ∀ {α₁ α₂ A} {P₁ P₂ Q₁ Q₂ Q₁′ : PTree E (ExtI E) (⊤ {ℓr})} {l}
     → Q₁ ─[ l ]─► Q₁′ → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂ → ICond α₁ α₂ A P₁ P₂ Q₁′ Q₂
icQ₁ st ic = record { ooP₁ = ic .ooP₁ ; ooP₂ = ic .ooP₂
                    ; ooQ₁ = OffersOnly.step (ic .ooQ₁) st ; ooQ₂ = ic .ooQ₂
                    ; sepP = Sep.stepR (ic .sepP) st ; sepQ = ic .sepQ }

-- ... along a step of Q₂
icQ₂ : ∀ {α₁ α₂ A} {P₁ P₂ Q₁ Q₂ Q₂′ : PTree E (ExtI E) (⊤ {ℓr})} {l}
     → Q₂ ─[ l ]─► Q₂′ → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂ → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂′
icQ₂ st ic = record { ooP₁ = ic .ooP₁ ; ooP₂ = ic .ooP₂
                    ; ooQ₁ = ic .ooQ₁ ; ooQ₂ = OffersOnly.step (ic .ooQ₂) st
                    ; sepP = ic .sepP ; sepQ = Sep.stepR (ic .sepQ) st }

-------------------------------------------------------------------------------------
-- Non-offer plumbing
-------------------------------------------------------------------------------------

-- Turn "this tree has no visible step on `(X,e)@a`" into the syntactic non-offer that
-- `Par-soloL` / `Par-soloR` consume.  `ret` / `sil` nodes offer nothing at all; a
-- `react` node that DID offer would give the very step assumed impossible.
noOffer : {T : PTree E (ExtI E) (⊤ {ℓr})} {X : Set ℓ} {e : E X} {a : X}
        → (∀ {T′ : PTree E (ExtI E) (⊤ {ℓr})}
             → T ─[ ev (evl (evLabel X e a)) ]─► T′ → ⊥)
        → viewV (PTree.force T) (X , e) a ≡ nothing
noOffer {T = T} {X = X} {e = e} {a = a} ns with PTree.force T in eqT
... | ret r       = refl
... | sil t       = refl
... | react v τc  with v (X , e) a in eqv
...   | nothing   = refl
...   | just t′   = ⊥-elim (ns (sVis {at = X , e} {a = a} eqT eqv))

-- Disjoint alphabets: a `α₁`-event can never be offered by an `α₂`-confined tree.
clash : ∀ {α₁ α₂ : Alpha} {U : PTree E (ExtI E) (⊤ {ℓr})} {X : Set ℓ} {e : E X} {a : X}
      → Disj α₁ α₂ → α₁ (X , e) a → OffersOnly α₂ U
      → ∀ {U′ : PTree E (ExtI E) (⊤ {ℓr})}
      → U ─[ ev (evl (evLabel X e a)) ]─► U′ → ⊥
clash dj p ooU st = dj _ _ p (OffersOnly.now ooU st)

-- mirror: a `α₂`-event can never be offered by an `α₁`-confined tree.
clash′ : ∀ {α₁ α₂ : Alpha} {U : PTree E (ExtI E) (⊤ {ℓr})} {X : Set ℓ} {e : E X} {a : X}
       → Disj α₁ α₂ → α₂ (X , e) a → OffersOnly α₁ U
       → ∀ {U′ : PTree E (ExtI E) (⊤ {ℓr})}
       → U ─[ ev (evl (evLabel X e a)) ]─► U′ → ⊥
clash′ dj p ooU st = dj _ _ (OffersOnly.now ooU st) p

-- An interleaving cannot step on an event neither operand offers.  (`evSync` is
-- vacuous at `∅ES`; `evBoth` still needs the LEFT operand to step.)
⦀-noStep : {U V : PTree E (ExtI E) (⊤ {ℓr})} {X : Set ℓ} {e : E X} {a : X}
         → (∀ {U′ : PTree E (ExtI E) (⊤ {ℓr})}
              → U ─[ ev (evl (evLabel X e a)) ]─► U′ → ⊥)
         → (∀ {V′ : PTree E (ExtI E) (⊤ {ℓr})}
              → V ─[ ev (evl (evLabel X e a)) ]─► V′ → ⊥)
         → ∀ {W : PTree E (ExtI E) (⊤ {ℓr})}
         → (U ⦀ V) ─[ ev (evl (evLabel X e a)) ]─► W → ⊥
⦀-noStep {U = U} {V = V} nu nv st with Par-ev-elim ∅ES tm U V st
... | evSync () _ _
... | evL    _  p   = nu p
... | evR    _  q   = nv q
... | evBoth _  p _ = nu p

-------------------------------------------------------------------------------------
-- The strong bisimulation
-------------------------------------------------------------------------------------

-- the law itself (forward-declared: the four transfer functions below corecurse into it)
Interchange : ∀ {α₁ α₂ : Alpha} (A : EventSet) → Disj α₁ α₂
            → (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr}))
            → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂
            → (Par A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂))
              ∼ (Par ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂))

-- The SAME bisimulation read right-to-left.  It exists only for guardedness: the
-- backward half must return `RHS-successor ∼ LHS-successor`, and wrapping the
-- corecursive call in `sbisim-sym` would put it under a function application, which
-- the productivity checker rejects.  Defined mutually with `Interchange` by swapping
-- the two transfer functions between `fwd` and `bwd`, so the corecursive call stays
-- syntactically under the `_,_` constructor.
Interchange-sym : ∀ {α₁ α₂ : Alpha} (A : EventSet) → Disj α₁ α₂
                → (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr}))
                → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂
                → (Par ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂))
                  ∼ (Par A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂))

-- FORWARD τ: a τ of the un-regrouped composite belongs to exactly one of the four
-- components; the regrouped composite replays it through the matching nesting.
ich-fwd-τ : ∀ {α₁ α₂ : Alpha} (A : EventSet) (dj : Disj α₁ α₂)
            (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr}))
          → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂
          → {M : PTree E (ExtI E) (⊤ {ℓr})}
          → (Par A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂)) ─[ τ ]─► M
          → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ]
              (((Par ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂)) ─[ τ ]─► M′) × (M ∼ M′))
ich-fwd-τ A dj P₁ P₂ Q₁ Q₂ ic st
  with Par-τ-elim A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) st
... | τL _ pτ refl with Par-τ-elim ∅ES tm P₁ P₂ pτ
...   | τL P₁′ p₁ refl =
        _ , Par-τ-L ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) (Par-τ-L A tm P₁ Q₁ p₁)
          , Interchange A dj P₁′ P₂ Q₁ Q₂ (icP₁ p₁ ic)
...   | τR P₂′ p₂ refl =
        _ , Par-τ-R ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) (Par-τ-L A tm P₂ Q₂ p₂)
          , Interchange A dj P₁ P₂′ Q₁ Q₂ (icP₂ p₂ ic)
ich-fwd-τ A dj P₁ P₂ Q₁ Q₂ ic st
    | τR _ qτ refl with Par-τ-elim ∅ES tm Q₁ Q₂ qτ
...   | τL Q₁′ q₁ refl =
        _ , Par-τ-L ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) (Par-τ-R A tm P₁ Q₁ q₁)
          , Interchange A dj P₁ P₂ Q₁′ Q₂ (icQ₁ q₁ ic)
...   | τR Q₂′ q₂ refl =
        _ , Par-τ-R ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) (Par-τ-R A tm P₂ Q₂ q₂)
          , Interchange A dj P₁ P₂ Q₁ Q₂′ (icQ₂ q₂ ic)

-- FORWARD visible/√.  Five outer cases:
--   evSync — the shared event is offered by one component on each side; `Disj` forces
--     the two to be the SAME component, so the regrouped side syncs INSIDE that
--     component and lifts the result past the (necessarily silent) other one;
--   evL / evR — a solo event of one family, again pinned to one component;
--   evBoth — impossible: it would need the two families to both offer an outside-`A`
--     event, which `Sep` (same component) or `Disj` (across components) forbids;
--   ev√ — all four components have terminated, so both sides emit √ and die.
ich-fwd-ev : ∀ {α₁ α₂ : Alpha} (A : EventSet) (dj : Disj α₁ α₂)
             (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr}))
           → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂
           → {M : PTree E (ExtI E) (⊤ {ℓr})} {e : Event√ (⊤ {ℓr})}
           → (Par A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂)) ─[ ev e ]─► M
           → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ]
               (((Par ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂)) ─[ ev e ]─► M′) × (M ∼ M′))
ich-fwd-ev A dj P₁ P₂ Q₁ Q₂ ic st
  with Par-ev-elim A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) st

-- ---- shared (`∈ A`) event: both families move ----
... | evSync cs pst qst
      with Par-ev-elim ∅ES tm P₁ P₂ pst | Par-ev-elim ∅ES tm Q₁ Q₂ qst
...   | evSync () _ _  | _
...   | _              | evSync () _ _
...   | evBoth _ p₁ p₂ | _ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooP₁) p₁) (OffersOnly.now (ic .ooP₂) p₂))
...   | evL _ p₁       | evBoth _ q₁ q₂ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooQ₁) q₁) (OffersOnly.now (ic .ooQ₂) q₂))
...   | evR _ p₂       | evBoth _ q₁ q₂ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooQ₁) q₁) (OffersOnly.now (ic .ooQ₂) q₂))
-- component 1 on both sides: sync inside component 1, lift past component 2
...   | evL _ p₁       | evL _ q₁ =
        _ , Par-soloL ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) (λ z → z)
              (Par-sync A tm P₁ Q₁ cs p₁ q₁)
              (noOffer (clash dj (OffersOnly.now (ic .ooP₁) p₁)
                                 (OffersOnly-Par A tm (ic .ooP₂) (ic .ooQ₂))))
          , Interchange A dj _ P₂ _ Q₂ (icQ₁ q₁ (icP₁ p₁ ic))
-- component 2 on both sides
...   | evR _ p₂       | evR _ q₂ =
        _ , Par-soloR ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) (λ z → z)
              (Par-sync A tm P₂ Q₂ cs p₂ q₂)
              (noOffer (clash′ dj (OffersOnly.now (ic .ooP₂) p₂)
                                  (OffersOnly-Par A tm (ic .ooP₁) (ic .ooQ₁))))
          , Interchange A dj P₁ _ Q₁ _ (icQ₂ q₂ (icP₂ p₂ ic))
-- CROSS-component synchronisation — the very behaviour `Disj` rules out
...   | evL _ p₁       | evR _ q₂ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooP₁) p₁) (OffersOnly.now (ic .ooQ₂) q₂))
...   | evR _ p₂       | evL _ q₁ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooQ₁) q₁) (OffersOnly.now (ic .ooP₂) p₂))

-- ---- solo (`∉ A`) event of the P-family ----
ich-fwd-ev A dj P₁ P₂ Q₁ Q₂ ic st
    | evL ¬cs pst with Par-ev-elim ∅ES tm P₁ P₂ pst
...   | evSync () _ _
...   | evBoth _ p₁ p₂ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooP₁) p₁) (OffersOnly.now (ic .ooP₂) p₂))
...   | evL _ p₁ =
        _ , Par-soloL ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) (λ z → z)
              (Par-soloL A tm P₁ Q₁ ¬cs p₁ (noOffer (λ q₁ → Sep.now (ic .sepP) ¬cs p₁ q₁)))
              (noOffer (clash dj (OffersOnly.now (ic .ooP₁) p₁)
                                 (OffersOnly-Par A tm (ic .ooP₂) (ic .ooQ₂))))
          , Interchange A dj _ P₂ Q₁ Q₂ (icP₁ p₁ ic)
...   | evR _ p₂ =
        _ , Par-soloR ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) (λ z → z)
              (Par-soloL A tm P₂ Q₂ ¬cs p₂ (noOffer (λ q₂ → Sep.now (ic .sepQ) ¬cs p₂ q₂)))
              (noOffer (clash′ dj (OffersOnly.now (ic .ooP₂) p₂)
                                  (OffersOnly-Par A tm (ic .ooP₁) (ic .ooQ₁))))
          , Interchange A dj P₁ _ Q₁ Q₂ (icP₂ p₂ ic)

-- ---- solo (`∉ A`) event of the Q-family ----
ich-fwd-ev A dj P₁ P₂ Q₁ Q₂ ic st
    | evR ¬cs qst with Par-ev-elim ∅ES tm Q₁ Q₂ qst
...   | evSync () _ _
...   | evBoth _ q₁ q₂ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooQ₁) q₁) (OffersOnly.now (ic .ooQ₂) q₂))
...   | evL _ q₁ =
        _ , Par-soloL ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) (λ z → z)
              (Par-soloR A tm P₁ Q₁ ¬cs q₁ (noOffer (λ p₁ → Sep.now (ic .sepP) ¬cs p₁ q₁)))
              (noOffer (clash dj (OffersOnly.now (ic .ooQ₁) q₁)
                                 (OffersOnly-Par A tm (ic .ooP₂) (ic .ooQ₂))))
          , Interchange A dj P₁ P₂ _ Q₂ (icQ₁ q₁ ic)
...   | evR _ q₂ =
        _ , Par-soloR ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) (λ z → z)
              (Par-soloR A tm P₂ Q₂ ¬cs q₂ (noOffer (λ p₂ → Sep.now (ic .sepQ) ¬cs p₂ q₂)))
              (noOffer (clash′ dj (OffersOnly.now (ic .ooQ₂) q₂)
                                  (OffersOnly-Par A tm (ic .ooP₁) (ic .ooQ₁))))
          , Interchange A dj P₁ P₂ Q₁ _ (icQ₂ q₂ ic)

-- ---- both families offer the same outside-`A` event: excluded ----
ich-fwd-ev A dj P₁ P₂ Q₁ Q₂ ic st
    | evBoth ¬cs pst qst
      with Par-ev-elim ∅ES tm P₁ P₂ pst | Par-ev-elim ∅ES tm Q₁ Q₂ qst
...   | evSync () _ _  | _
...   | _              | evSync () _ _
...   | evBoth _ p₁ p₂ | _ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooP₁) p₁) (OffersOnly.now (ic .ooP₂) p₂))
...   | evL _ p₁       | evBoth _ q₁ q₂ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooQ₁) q₁) (OffersOnly.now (ic .ooQ₂) q₂))
...   | evR _ p₂       | evBoth _ q₁ q₂ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooQ₁) q₁) (OffersOnly.now (ic .ooQ₂) q₂))
...   | evL _ p₁       | evL _ q₁ = ⊥-elim (Sep.now (ic .sepP) ¬cs p₁ q₁)
...   | evR _ p₂       | evR _ q₂ = ⊥-elim (Sep.now (ic .sepQ) ¬cs p₂ q₂)
...   | evL _ p₁       | evR _ q₂ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooP₁) p₁) (OffersOnly.now (ic .ooQ₂) q₂))
...   | evR _ p₂       | evL _ q₁ =
        ⊥-elim (dj _ _ (OffersOnly.now (ic .ooQ₁) q₁) (OffersOnly.now (ic .ooP₂) p₂))

-- ---- joint termination ----
ich-fwd-ev A dj P₁ P₂ Q₁ Q₂ ic st
    | ev√ fp fq with Par-force-ret-inv ∅ES tm fp | Par-force-ret-inv ∅ES tm fq
...   | _ , _ , fp₁ , fp₂ , refl | _ , _ , fq₁ , fq₂ , refl =
        deadlock
        , sRet (fPar-rr ∅ES tm (fPar-rr A tm fp₁ fq₁) (fPar-rr A tm fp₂ fq₂))
        , sbisim-refl deadlock

-- BACKWARD τ: mirror of `ich-fwd-τ`, decomposing the regrouped composite instead.
ich-bwd-τ : ∀ {α₁ α₂ : Alpha} (A : EventSet) (dj : Disj α₁ α₂)
            (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr}))
          → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂
          → {M : PTree E (ExtI E) (⊤ {ℓr})}
          → (Par ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂)) ─[ τ ]─► M
          → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ]
              (((Par A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂)) ─[ τ ]─► M′) × (M ∼ M′))
ich-bwd-τ A dj P₁ P₂ Q₁ Q₂ ic st
  with Par-τ-elim ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) st
... | τL _ lτ refl with Par-τ-elim A tm P₁ Q₁ lτ
...   | τL P₁′ p₁ refl =
        _ , Par-τ-L A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) (Par-τ-L ∅ES tm P₁ P₂ p₁)
          , Interchange-sym A dj P₁′ P₂ Q₁ Q₂ (icP₁ p₁ ic)
...   | τR Q₁′ q₁ refl =
        _ , Par-τ-R A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) (Par-τ-L ∅ES tm Q₁ Q₂ q₁)
          , Interchange-sym A dj P₁ P₂ Q₁′ Q₂ (icQ₁ q₁ ic)
ich-bwd-τ A dj P₁ P₂ Q₁ Q₂ ic st
    | τR _ rτ refl with Par-τ-elim A tm P₂ Q₂ rτ
...   | τL P₂′ p₂ refl =
        _ , Par-τ-L A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) (Par-τ-R ∅ES tm P₁ P₂ p₂)
          , Interchange-sym A dj P₁ P₂′ Q₁ Q₂ (icP₂ p₂ ic)
...   | τR Q₂′ q₂ refl =
        _ , Par-τ-R A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) (Par-τ-R ∅ES tm Q₁ Q₂ q₂)
          , Interchange-sym A dj P₁ P₂ Q₁ Q₂′ (icQ₂ q₂ ic)

-- BACKWARD visible/√.  The regrouped side decomposes first into a component, then
-- into a family; the un-regrouped side lifts each move solo through its interleaving
-- (the sibling component never offers the event, by `Disj`) before pairing it with
-- the outer `∥⇘A⇙`.
ich-bwd-ev : ∀ {α₁ α₂ : Alpha} (A : EventSet) (dj : Disj α₁ α₂)
             (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr}))
           → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂
           → {M : PTree E (ExtI E) (⊤ {ℓr})} {e : Event√ (⊤ {ℓr})}
           → (Par ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂)) ─[ ev e ]─► M
           → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ]
               (((Par A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂)) ─[ ev e ]─► M′) × (M ∼ M′))
ich-bwd-ev A dj P₁ P₂ Q₁ Q₂ ic st
  with Par-ev-elim ∅ES tm (Par A tm P₁ Q₁) (Par A tm P₂ Q₂) st

... | evSync () _ _

-- ---- the move is component 1's ----
... | evL _ lst with Par-ev-elim A tm P₁ Q₁ lst
...   | evBoth ¬cs p₁ q₁ = ⊥-elim (Sep.now (ic .sepP) ¬cs p₁ q₁)
...   | evSync cs p₁ q₁ =
        _ , Par-sync A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) cs
              (Par-soloL ∅ES tm P₁ P₂ (λ z → z) p₁
                 (noOffer (clash dj (OffersOnly.now (ic .ooP₁) p₁) (ic .ooP₂))))
              (Par-soloL ∅ES tm Q₁ Q₂ (λ z → z) q₁
                 (noOffer (clash dj (OffersOnly.now (ic .ooQ₁) q₁) (ic .ooQ₂))))
          , Interchange-sym A dj _ P₂ _ Q₂ (icQ₁ q₁ (icP₁ p₁ ic))
...   | evL ¬cs p₁ =
        _ , Par-soloL A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) ¬cs
              (Par-soloL ∅ES tm P₁ P₂ (λ z → z) p₁
                 (noOffer (clash dj (OffersOnly.now (ic .ooP₁) p₁) (ic .ooP₂))))
              (noOffer (⦀-noStep (λ q₁ → Sep.now (ic .sepP) ¬cs p₁ q₁)
                                 (clash dj (OffersOnly.now (ic .ooP₁) p₁) (ic .ooQ₂))))
          , Interchange-sym A dj _ P₂ Q₁ Q₂ (icP₁ p₁ ic)
...   | evR ¬cs q₁ =
        _ , Par-soloR A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) ¬cs
              (Par-soloL ∅ES tm Q₁ Q₂ (λ z → z) q₁
                 (noOffer (clash dj (OffersOnly.now (ic .ooQ₁) q₁) (ic .ooQ₂))))
              (noOffer (⦀-noStep (λ p₁ → Sep.now (ic .sepP) ¬cs p₁ q₁)
                                 (clash dj (OffersOnly.now (ic .ooQ₁) q₁) (ic .ooP₂))))
          , Interchange-sym A dj P₁ P₂ _ Q₂ (icQ₁ q₁ ic)

-- ---- the move is component 2's ----
ich-bwd-ev A dj P₁ P₂ Q₁ Q₂ ic st
    | evR _ rst with Par-ev-elim A tm P₂ Q₂ rst
...   | evBoth ¬cs p₂ q₂ = ⊥-elim (Sep.now (ic .sepQ) ¬cs p₂ q₂)
...   | evSync cs p₂ q₂ =
        _ , Par-sync A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) cs
              (Par-soloR ∅ES tm P₁ P₂ (λ z → z) p₂
                 (noOffer (clash′ dj (OffersOnly.now (ic .ooP₂) p₂) (ic .ooP₁))))
              (Par-soloR ∅ES tm Q₁ Q₂ (λ z → z) q₂
                 (noOffer (clash′ dj (OffersOnly.now (ic .ooQ₂) q₂) (ic .ooQ₁))))
          , Interchange-sym A dj P₁ _ Q₁ _ (icQ₂ q₂ (icP₂ p₂ ic))
...   | evL ¬cs p₂ =
        _ , Par-soloL A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) ¬cs
              (Par-soloR ∅ES tm P₁ P₂ (λ z → z) p₂
                 (noOffer (clash′ dj (OffersOnly.now (ic .ooP₂) p₂) (ic .ooP₁))))
              (noOffer (⦀-noStep (clash′ dj (OffersOnly.now (ic .ooP₂) p₂) (ic .ooQ₁))
                                 (λ q₂ → Sep.now (ic .sepQ) ¬cs p₂ q₂)))
          , Interchange-sym A dj P₁ _ Q₁ Q₂ (icP₂ p₂ ic)
...   | evR ¬cs q₂ =
        _ , Par-soloR A tm (Par ∅ES tm P₁ P₂) (Par ∅ES tm Q₁ Q₂) ¬cs
              (Par-soloR ∅ES tm Q₁ Q₂ (λ z → z) q₂
                 (noOffer (clash′ dj (OffersOnly.now (ic .ooQ₂) q₂) (ic .ooQ₁))))
              (noOffer (⦀-noStep (clash′ dj (OffersOnly.now (ic .ooQ₂) q₂) (ic .ooP₁))
                                 (λ p₂ → Sep.now (ic .sepQ) ¬cs p₂ q₂)))
          , Interchange-sym A dj P₁ P₂ Q₁ _ (icQ₂ q₂ ic)

-- ---- both components offer the same outside-`A` event: excluded by `Disj` ----
ich-bwd-ev A dj P₁ P₂ Q₁ Q₂ ic st
    | evBoth _ lst rst =
      ⊥-elim (dj _ _ (OffersOnly.now (OffersOnly-Par A tm (ic .ooP₁) (ic .ooQ₁)) lst)
                     (OffersOnly.now (OffersOnly-Par A tm (ic .ooP₂) (ic .ooQ₂)) rst))

-- ---- joint termination ----
ich-bwd-ev A dj P₁ P₂ Q₁ Q₂ ic st
    | ev√ fl fr with Par-force-ret-inv A tm fl | Par-force-ret-inv A tm fr
...   | _ , _ , fp₁ , fq₁ , refl | _ , _ , fp₂ , fq₂ , refl =
        deadlock
        , sRet (fPar-rr A tm (fPar-rr ∅ES tm fp₁ fp₂) (fPar-rr ∅ES tm fq₁ fq₂))
        , sbisim-refl deadlock

Interchange A dj P₁ P₂ Q₁ Q₂ ic .Sbisim.fwd .SSimF.on-ev  = ich-fwd-ev A dj P₁ P₂ Q₁ Q₂ ic
Interchange A dj P₁ P₂ Q₁ Q₂ ic .Sbisim.fwd .SSimF.on-tau = ich-fwd-τ  A dj P₁ P₂ Q₁ Q₂ ic
Interchange A dj P₁ P₂ Q₁ Q₂ ic .Sbisim.bwd .SSimF.on-ev  = ich-bwd-ev A dj P₁ P₂ Q₁ Q₂ ic
Interchange A dj P₁ P₂ Q₁ Q₂ ic .Sbisim.bwd .SSimF.on-tau = ich-bwd-τ  A dj P₁ P₂ Q₁ Q₂ ic

-- the mirror: the two transfer functions swap sides
Interchange-sym A dj P₁ P₂ Q₁ Q₂ ic .Sbisim.fwd .SSimF.on-ev  = ich-bwd-ev A dj P₁ P₂ Q₁ Q₂ ic
Interchange-sym A dj P₁ P₂ Q₁ Q₂ ic .Sbisim.fwd .SSimF.on-tau = ich-bwd-τ  A dj P₁ P₂ Q₁ Q₂ ic
Interchange-sym A dj P₁ P₂ Q₁ Q₂ ic .Sbisim.bwd .SSimF.on-ev  = ich-fwd-ev A dj P₁ P₂ Q₁ Q₂ ic
Interchange-sym A dj P₁ P₂ Q₁ Q₂ ic .Sbisim.bwd .SSimF.on-tau = ich-fwd-τ  A dj P₁ P₂ Q₁ Q₂ ic

-------------------------------------------------------------------------------------
-- The law in operator notation, and its liftings
-------------------------------------------------------------------------------------

-- interface parallel distributes over interleaving, component-wise (STRONG bisim)
Par-interchange : ∀ {α₁ α₂ : Alpha} (A : EventSet) → Disj α₁ α₂
                → (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr}))
                → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂
                → ((P₁ ⦀ P₂) ∥⇘ A ⇙ (Q₁ ⦀ Q₂)) ∼ ((P₁ ∥⇘ A ⇙ Q₁) ⦀ (P₂ ∥⇘ A ⇙ Q₂))
Par-interchange = Interchange

-- ... hence at divergence-respecting weak bisimulation
Par-interchange-DR : ∀ {α₁ α₂ : Alpha} (A : EventSet) → Disj α₁ α₂
                   → (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr}))
                   → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂
                   → ((P₁ ⦀ P₂) ∥⇘ A ⇙ (Q₁ ⦀ Q₂)) ≈DR ((P₁ ∥⇘ A ⇙ Q₁) ⦀ (P₂ ∥⇘ A ⇙ Q₂))
Par-interchange-DR A dj P₁ P₂ Q₁ Q₂ ic =
  sbisim→drbisim (Par-interchange A dj P₁ P₂ Q₁ Q₂ ic)

-- ... and hence in the failures-divergences model
Par-interchange-FD : ∀ {α₁ α₂ : Alpha} (A : EventSet) → Disj α₁ α₂
                   → (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr}))
                   → ICond α₁ α₂ A P₁ P₂ Q₁ Q₂
                   → ((P₁ ⦀ P₂) ∥⇘ A ⇙ (Q₁ ⦀ Q₂)) ≈FD ((P₁ ∥⇘ A ⇙ Q₁) ⦀ (P₂ ∥⇘ A ⇙ Q₂))
Par-interchange-FD A dj P₁ P₂ Q₁ Q₂ ic =
  drbisim→≈FD (Par-interchange-DR A dj P₁ P₂ Q₁ Q₂ ic)

-------------------------------------------------------------------------------------
-- The `⦀Fin⁺` FOLD version
--
-- Lifting the binary law to the replicated interleaving needs the tail fold's `Sep`
-- (the binary law's `sepQ` field, instantiated at the two tails), which is NOT one of
-- the per-index hypotheses.  `sep-⦀` / `sep-⦀Fin⁺` below derive it: pairs from
-- DIFFERENT components are separated by `Disj`, pairs from the SAME component by that
-- component's own `Sep`.
--
-- The fold law itself is stated at `≈DR`, not `∼`: the induction step must rewrite
-- UNDER an interleaving, and the repo's only interleaving congruence (`cong-⦀`) is a
-- ≈DR one.  The binary law remains the stronger `∼` statement above; only the
-- assembly is weaker.
-------------------------------------------------------------------------------------

-- `deadlock` takes no step at all (its node is `react` with both maps empty)
deadlock-no-step : ∀ {l} {M : PTree E (ExtI E) (⊤ {ℓr})}
                 → (deadlock {E = E} {I = ExtI E} {R = ⊤ {ℓr}}) ─[ l ]─► M → ⊥
deadlock-no-step (sRet ())
deadlock-no-step (sSil ())
deadlock-no-step (sVis refl ())
deadlock-no-step (sTau refl ())

-- ... so it is `Sep` with anything, on either side
sep-deadlock-L : (A : EventSet) {Y : PTree E (ExtI E) (⊤ {ℓr})}
               → Sep A (deadlock {E = E} {I = ExtI E} {R = ⊤ {ℓr}}) Y
sep-deadlock-L A .Sep.now _ p _ = ⊥-elim (deadlock-no-step p)
sep-deadlock-L A .Sep.stepL p   = ⊥-elim (deadlock-no-step p)
sep-deadlock-L A .Sep.stepR _   = sep-deadlock-L A

-- mirror
sep-deadlock-R : (A : EventSet) {X : PTree E (ExtI E) (⊤ {ℓr})}
               → Sep A X (deadlock {E = E} {I = ExtI E} {R = ⊤ {ℓr}})
sep-deadlock-R A .Sep.now _ _ q = ⊥-elim (deadlock-no-step q)
sep-deadlock-R A .Sep.stepL _   = sep-deadlock-R A
sep-deadlock-R A .Sep.stepR q   = ⊥-elim (deadlock-no-step q)

-- `Sep` of two interleavings, component-wise.  `now`: a both-offer would pair either
-- two like components (excluded by that component's `Sep`) or two unlike ones
-- (excluded by `Disj`).  `stepL`/`stepR`: the `evBoth` residual — an overlap node —
-- never arises, since it needs ONE side's two components to both offer, which `Disj`
-- forbids; joint termination lands in `deadlock`.
sep-⦀ : ∀ {α β : Alpha} (A : EventSet)
        (X₀ Xt Y₀ Yt : PTree E (ExtI E) (⊤ {ℓr}))
      → Disj α β
      → OffersOnly α X₀ → OffersOnly β Xt
      → OffersOnly α Y₀ → OffersOnly β Yt
      → Sep A X₀ Y₀ → Sep A Xt Yt
      → Sep A (X₀ ⦀ Xt) (Y₀ ⦀ Yt)

sep-⦀ A X₀ Xt Y₀ Yt dj oX₀ oXt oY₀ oYt s₀ st .Sep.now ¬cs pst qst
  with Par-ev-elim ∅ES tm X₀ Xt pst | Par-ev-elim ∅ES tm Y₀ Yt qst
... | evSync ()  _  _  | _
... | _                | evSync ()  _  _
... | evBoth _ p₀ pt   | _ = dj _ _ (OffersOnly.now oX₀ p₀) (OffersOnly.now oXt pt)
... | evL    _ p₀      | evBoth _ q₀ qt =
      dj _ _ (OffersOnly.now oY₀ q₀) (OffersOnly.now oYt qt)
... | evR    _ pt      | evBoth _ q₀ qt =
      dj _ _ (OffersOnly.now oY₀ q₀) (OffersOnly.now oYt qt)
... | evL    _ p₀      | evL _ q₀ = Sep.now s₀ ¬cs p₀ q₀
... | evR    _ pt      | evR _ qt = Sep.now st ¬cs pt qt
... | evL    _ p₀      | evR _ qt = dj _ _ (OffersOnly.now oX₀ p₀) (OffersOnly.now oYt qt)
... | evR    _ pt      | evL _ q₀ = dj _ _ (OffersOnly.now oY₀ q₀) (OffersOnly.now oXt pt)

sep-⦀ A X₀ Xt Y₀ Yt dj oX₀ oXt oY₀ oYt s₀ st .Sep.stepL {l = τ} stp
  with Par-τ-elim ∅ES tm X₀ Xt stp
... | τL X₀′ p refl =
      sep-⦀ A X₀′ Xt Y₀ Yt dj (OffersOnly.step oX₀ p) oXt oY₀ oYt (Sep.stepL s₀ p) st
... | τR Xt′ p refl =
      sep-⦀ A X₀ Xt′ Y₀ Yt dj oX₀ (OffersOnly.step oXt p) oY₀ oYt s₀ (Sep.stepL st p)
sep-⦀ A X₀ Xt Y₀ Yt dj oX₀ oXt oY₀ oYt s₀ st .Sep.stepL {l = ev e} stp
  with Par-ev-elim ∅ES tm X₀ Xt stp
... | evSync ()  _ _
... | evL    _   p =
      sep-⦀ A _ Xt Y₀ Yt dj (OffersOnly.step oX₀ p) oXt oY₀ oYt (Sep.stepL s₀ p) st
... | evR    _   p =
      sep-⦀ A X₀ _ Y₀ Yt dj oX₀ (OffersOnly.step oXt p) oY₀ oYt s₀ (Sep.stepL st p)
... | evBoth _ p₀ pt =
      ⊥-elim (dj _ _ (OffersOnly.now oX₀ p₀) (OffersOnly.now oXt pt))
... | ev√    _ _   = sep-deadlock-L A

sep-⦀ A X₀ Xt Y₀ Yt dj oX₀ oXt oY₀ oYt s₀ st .Sep.stepR {l = τ} stq
  with Par-τ-elim ∅ES tm Y₀ Yt stq
... | τL Y₀′ q refl =
      sep-⦀ A X₀ Xt Y₀′ Yt dj oX₀ oXt (OffersOnly.step oY₀ q) oYt (Sep.stepR s₀ q) st
... | τR Yt′ q refl =
      sep-⦀ A X₀ Xt Y₀ Yt′ dj oX₀ oXt oY₀ (OffersOnly.step oYt q) s₀ (Sep.stepR st q)
sep-⦀ A X₀ Xt Y₀ Yt dj oX₀ oXt oY₀ oYt s₀ st .Sep.stepR {l = ev e} stq
  with Par-ev-elim ∅ES tm Y₀ Yt stq
... | evSync ()  _ _
... | evL    _   q =
      sep-⦀ A X₀ Xt _ Yt dj oX₀ oXt (OffersOnly.step oY₀ q) oYt (Sep.stepR s₀ q) st
... | evR    _   q =
      sep-⦀ A X₀ Xt Y₀ _ dj oX₀ oXt oY₀ (OffersOnly.step oYt q) s₀ (Sep.stepR st q)
... | evBoth _ q₀ qt =
      ⊥-elim (dj _ _ (OffersOnly.now oY₀ q₀) (OffersOnly.now oYt qt))
... | ev√    _ _   = sep-deadlock-R A

-- `Sep` of the two non-empty folds, by induction on the index bound
sep-⦀Fin⁺ : ∀ {n} (A : EventSet) (αs : Fin (suc n) → Alpha)
             (P Q : Fin (suc n) → PTree E (ExtI E) (⊤ {ℓr}))
           → (∀ i j → i ≢ j → Disj (αs i) (αs j))
           → (∀ i → OffersOnly (αs i) (P i))
           → (∀ i → OffersOnly (αs i) (Q i))
           → (∀ i → Sep A (P i) (Q i))
           → Sep A (⦀Fin⁺ n P) (⦀Fin⁺ n Q)
sep-⦀Fin⁺ {n = zero}  A αs P Q disj oP oQ sep = sep fzero
sep-⦀Fin⁺ {n = suc n} A αs P Q disj oP oQ sep =
  sep-⦀ A (P fzero) (⦀Fin⁺ n (λ i → P (fsuc i)))
          (Q fzero) (⦀Fin⁺ n (λ i → Q (fsuc i)))
        hdDisj
        (oP fzero) (OffersOnly-⦀Fin⁺ (λ i → oP (fsuc i)))
        (oQ fzero) (OffersOnly-⦀Fin⁺ (λ i → oQ (fsuc i)))
        (sep fzero)
        (sep-⦀Fin⁺ A (λ i → αs (fsuc i)) (λ i → P (fsuc i)) (λ i → Q (fsuc i))
                   (λ i j i≢j → disj (fsuc i) (fsuc j) (λ e → i≢j (suc-injective e)))
                   (λ i → oP (fsuc i)) (λ i → oQ (fsuc i)) (λ i → sep (fsuc i)))
  where
  -- the head alphabet clashes with nothing in the tail union
  hdDisj : Disj (αs fzero) (unionAlpha (λ i → αs (fsuc i)))
  hdDisj at a p (j , q) = disj fzero (fsuc j) (λ ()) at a p q

-- THE FOLD LAW: an interface parallel over two replicated interleavings regroups
-- index-wise.  Induction on the bound: the binary law peels the head pair off both
-- folds, then `cong-⦀` rewrites the tail with the induction hypothesis (its three
-- `Sep ∅ES` obligations all come from head-vs-tail-union disjointness, exactly as in
-- `cong-⦀Fin⁺`).
Interchange-⦀Fin⁺ : ∀ {n} (A : EventSet) (αs : Fin (suc n) → Alpha)
                    (P Q : Fin (suc n) → PTree E (ExtI E) (⊤ {ℓr}))
                  → (∀ i j → i ≢ j → Disj (αs i) (αs j))
                  → (∀ i → OffersOnly (αs i) (P i))
                  → (∀ i → OffersOnly (αs i) (Q i))
                  → (∀ i → Sep A (P i) (Q i))
                  → ((⦀Fin⁺ n P) ∥⇘ A ⇙ (⦀Fin⁺ n Q))
                    ≈DR (⦀Fin⁺ n (λ i → P i ∥⇘ A ⇙ Q i))
Interchange-⦀Fin⁺ {n = zero}  A αs P Q disj oP oQ sep = drbisim-refl _
Interchange-⦀Fin⁺ {n = suc n} A αs P Q disj oP oQ sep =
  drbisim-trans
    (Par-interchange-DR A hdDisj (P fzero) Pt (Q fzero) Qt
       (record { ooP₁ = oP fzero ; ooP₂ = oPt ; ooQ₁ = oQ fzero ; ooQ₂ = oQt
               ; sepP = sep fzero ; sepQ = tailSep }))
    (cong-⦀ (sep-from-OffersOnly ∅ES hdSep oHead oPQt)
            (sep-from-OffersOnly ∅ES hdSep oHead oPQt)
            (sep-from-OffersOnly ∅ES hdSep oHead oFold)
            (drbisim-refl _) ih)
  where
  -- the two tail folds and their union-alphabet confinement
  Pt = ⦀Fin⁺ n (λ i → P (fsuc i))
  Qt = ⦀Fin⁺ n (λ i → Q (fsuc i))
  oPt = OffersOnly-⦀Fin⁺ (λ i → oP (fsuc i))
  oQt = OffersOnly-⦀Fin⁺ (λ i → oQ (fsuc i))
  -- head alphabet vs the tail union
  hdDisj : Disj (αs fzero) (unionAlpha (λ i → αs (fsuc i)))
  hdDisj at a p (j , q) = disj fzero (fsuc j) (λ ()) at a p q
  -- the tail folds are `Sep`, by the lemma above
  tailSep = sep-⦀Fin⁺ A (λ i → αs (fsuc i)) (λ i → P (fsuc i)) (λ i → Q (fsuc i))
                      (λ i j i≢j → disj (fsuc i) (fsuc j) (λ e → i≢j (suc-injective e)))
                      (λ i → oP (fsuc i)) (λ i → oQ (fsuc i)) (λ i → sep (fsuc i))
  -- the induction hypothesis, at the tail
  ih = Interchange-⦀Fin⁺ A (λ i → αs (fsuc i)) (λ i → P (fsuc i)) (λ i → Q (fsuc i))
                         (λ i j i≢j → disj (fsuc i) (fsuc j) (λ e → i≢j (suc-injective e)))
                         (λ i → oP (fsuc i)) (λ i → oQ (fsuc i)) (λ i → sep (fsuc i))
  -- the two right-hand operands `cong-⦀` sees, both confined to the tail union
  oPQt = OffersOnly-Par A tm oPt oQt
  oFold = OffersOnly-⦀Fin⁺ (λ i → OffersOnly-Par A tm (oP (fsuc i)) (oQ (fsuc i)))
  -- the head composite, confined to the head alphabet
  oHead = OffersOnly-Par A tm (oP fzero) (oQ fzero)
  -- head-vs-tail-union clash, in the shape `sep-from-OffersOnly` consumes
  hdSep : ∀ {at a} → ¬ ∅ES .mem at a
        → αs fzero at a → unionAlpha (λ i → αs (fsuc i)) at a → ⊥
  hdSep _ p q = hdDisj _ _ p q

-- ... and in the failures-divergences model
Interchange-⦀Fin⁺-FD : ∀ {n} (A : EventSet) (αs : Fin (suc n) → Alpha)
                       (P Q : Fin (suc n) → PTree E (ExtI E) (⊤ {ℓr}))
                     → (∀ i j → i ≢ j → Disj (αs i) (αs j))
                     → (∀ i → OffersOnly (αs i) (P i))
                     → (∀ i → OffersOnly (αs i) (Q i))
                     → (∀ i → Sep A (P i) (Q i))
                     → ((⦀Fin⁺ n P) ∥⇘ A ⇙ (⦀Fin⁺ n Q))
                       ≈FD (⦀Fin⁺ n (λ i → P i ∥⇘ A ⇙ Q i))
Interchange-⦀Fin⁺-FD A αs P Q disj oP oQ sep =
  drbisim→≈FD (Interchange-⦀Fin⁺ A αs P Q disj oP oQ sep)
