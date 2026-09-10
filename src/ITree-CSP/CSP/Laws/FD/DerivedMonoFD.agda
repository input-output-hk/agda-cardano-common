{-# OPTIONS --guardedness #-}

-- FACT-SHAPED (`⊑FD → ⊑FD`) monotonicity for the three DERIVED operators:
--
--   `＆-mono-⊑FD`      guard          `b ＆ P    = guard b >> P`      (CSP.Operators:348)
--   `◁▷-mono-⊑FD`      conditional    `P ◁ b ▷ Q = if b then P else Q`(CSP.Operators:123)
--   `Output-mono-⊑FD`  output prefix  `e ! v ⟶ P`                    (CSP.Operators:181)
--
-- All three are TRUE PRECONGRUENCES (shape 2 in `CSP.Laws.FD.IChoiceMonoFD`'s taxonomy):
-- `⊑FD` facts in, `⊑FD` fact out, unconditionally.
--
-- WHY THEY LIVE TOGETHER, AND NOT IN `ChoiceRefine`.  `Output-mono-⊑FD` is the analogue
-- of `CSP.Laws.FD.ChoiceRefine.⟶₀-mono-⊑FD`, but it cannot REUSE it: `Output` and
-- `Prefix₀` share the event index `(A , e)` and differ in the OFFER MAP — `Output-cont`
-- fires on the single carried value `v` (an extra `x ≟ v` decision, hence the
-- `⦃ DecEq A ⦄`), where `Prefix-cont` fires on every value.  So the whole
-- failures/divergences decomposition of `Prefix₀`
-- (`CSP.Laws.FD.FDLawsPrefixDist`, :53-167) has to be redone for `Output`, which is the
-- bulk of this file; putting ~90 lines of `Output` plumbing inside `ChoiceRefine` (a
-- 60-line module about `⊓`-vs-`□` refinement) would swamp it, and putting it in
-- `FDLawsPrefixDist` (whose subject is `⊓`-distribution over prefix) would be off-topic.
-- The two `Bool`-split laws are one-liners and are grouped here as the other two
-- derived-operator precongruences.
--
-- THE `Bool` SPLITS ARE NOT QUITE FREE.  `b ＆ P` is `guard b >> P`, and BIND HAS NO
-- ETA: `force (Skip >> P) ≡ force P` holds by `refl`, but `Skip >> P` and `P` are
-- DIFFERENT trees (`PTree` is a coinductive record, so no η).  Crossing that gap is
-- `force-≡→⊑FD`: force-equal trees are ⊑FD-interchangeable, because every LTS rule reads
-- the source only through `force`.  It used to be a LOCAL helper here (routed through
-- `CSP.Laws.FD.BindFD`'s `cross-fail-force-eq` / `cross-div-force-eq`); it is now HOISTED
-- to `Semantics.FailuresDivergences`, beside `⊑FD-refl` / `⊑FD-trans`, and proved there
-- directly over the LTS — the statement is generic in `E`/`I` and needs nothing
-- CSP-specific.  It is the FD analogue of
-- `CSP.Laws.Traces.TraceLawsGuard.force-≡→traces-⊆` (same law at `⊑T`, for `＆-mono-⊑ᵀ`)
-- and of `CSP.Laws.FD.SeqLaws.sbisim-force-eq` (same law at `∼`).  The
-- `false` branch is force-equal on BOTH sides at once: `Stop >> P` deadlocks
-- independently of `P`.
--
-- POSTULATES: none local.  Inherited: NONE — `agda --safe CSP/Laws/FD/DerivedMonoFD.agda`
-- exits 0, so the whole import closure is postulate-free (the closure is
-- `Process_Trees` + `CSP.Operators` + seven `Semantics.*` modules, nothing else — the
-- `BindFD` dependency went away with the hoist).  The `Output` half is built directly
-- over the LTS; the `Bool` half is `force-≡→⊑FD` from `Semantics.FailuresDivergences`
-- (still `--safe`: that module's closure is `Semantics.{LTS,Failures,Refusals,WeakBisim,
-- DRBisim,Stability}` only — in particular it does NOT reach `Semantics.DRImpliesFD`).
-- `stable-no-τ` is taken from `Semantics.Stability` rather
-- than from `Semantics.DRImpliesFD` (which re-exports it) precisely to keep that clean.

open import Level using (Level)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.FD.DerivedMonoFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Offers; Refuses)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; failures⊥; _⊇F⊥_; _⊇D_; _⊑FD_; ⊑FD-trans; force-≡→⊑FD)
open import Semantics.Stability           {E = E} {I = ExtI E} using (stable-no-τ)

private
  variable
    ℓr ℓx : Level
    A : Set ℓ
    R : Set ℓr

-------------------------------------------------------------------------------------
-- PART 1 : the two `Bool` splits.
-------------------------------------------------------------------------------------

-- the guard is a ⊑FD-precongruence in its body: `true` routes through the force-equal
-- `P` (bind is force-transparent at `ret`), `false` gives two force-equal deadlocks
＆-mono-⊑FD : (b : Bool) {P Q : PTree E (ExtI E) R}
            → P ⊑FD Q → (b ＆ P) ⊑FD (b ＆ Q)
＆-mono-⊑FD true  h = ⊑FD-trans (force-≡→⊑FD refl) (⊑FD-trans h (force-≡→⊑FD refl))
＆-mono-⊑FD false h = force-≡→⊑FD refl

-- conditional choice is a ⊑FD-precongruence in both branches — it IS `if_then_else_`,
-- so each `b` just selects the matching hypothesis
◁▷-mono-⊑FD : (b : Bool) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
            → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂ → (P₁ ◁ b ▷ Q₁) ⊑FD (P₂ ◁ b ▷ Q₂)
◁▷-mono-⊑FD true  hP hQ = hP
◁▷-mono-⊑FD false hP hQ = hQ

-------------------------------------------------------------------------------------
-- PART 2 : the `Output` decomposition (the `Prefix₀` development of
-- `CSP.Laws.FD.FDLawsPrefixDist` redone for the single-value offer map).
-------------------------------------------------------------------------------------

-- the matching output branch fires: a freshly built `Output-cont` reduces neither
-- `E-≟ (A , e) (A , e)` nor `v ≟ v` abstractly (cf. `CSP.Laws.Bisim.Congruence.pc-just`)
oc-just : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (P : PTree E (ExtI E) R)
        → Output-cont e v P (A , e) v ≡ just P
oc-just {A = A} e v P with E-≟ (A , e) (A , e)
... | no  neq  = ⊥-elim (neq refl)
... | yes refl with v ≟ v
...   | yes _   = refl
...   | no  neq = ⊥-elim (neq refl)

-- an output node is stable (its τ-part is `∅t`)
output-stable : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C : PTree E (ExtI E) R)
              → isStable (Output e v C)
output-stable e v C _ _ = refl

-- every big-step out of an output node is either empty or peels the SINGLE event
-- `evLabel A e v` (no other carried value fires)
output-⟹-inv : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C : PTree E (ExtI E) R)
                {s : List (Event√ R)} {W : PTree E (ExtI E) R}
              → (Output e v C) ⟹⟨ s ⟩ W
              → (W ≡ Output e v C × s ≡ [])
              ⊎ (Σ[ t ∈ List (Event√ R) ]
                   (s ≡ evl (evLabel A e v) ∷ t × C ⟹⟨ t ⟩ W))
output-⟹-inv e v C ⟹-refl              = inj₁ (refl , refl)
output-⟹-inv e v C (⟹-τ (sSil ()) _)
output-⟹-inv e v C (⟹-τ (sTau refl ()) _)
output-⟹-inv e v C (⟹-ev (sRet ()) _)
output-⟹-inv {A = A} e v C (⟹-ev (sVis {at = at} {a = x} refl br) rest)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with x ≟ v
...   | no _     = case br of λ ()
...   | yes refl with br
...      | refl = inj₂ (_ , refl , rest)

-------------------------------------------------------------------------------------
-- Offers / refusals of an output node are CONTINUATION-INDEPENDENT (as for prefix: the
-- offer map's DOMAIN — here the single pair `((A , e) , v)` — does not mention `C`).
-------------------------------------------------------------------------------------

output-offers : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C D : PTree E (ExtI E) R)
                {l : Event√ R}
              → Offers (Output e v C) l → Offers (Output e v D) l
output-offers e v C D (_ , sRet ())
output-offers {A = A} e v C D (W , sVis {at = at} {a = x} refl br)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with x ≟ v
...   | no _     = case br of λ ()
...   | yes refl = D , sVis {at = A , e} {a = v} refl (oc-just e v D)

output-refuses : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C D : PTree E (ExtI E) R)
                 {X : Event√ R → Set ℓx}
               → Refuses (Output e v C) X → Refuses (Output e v D) X
output-refuses e v C D (_ , noOff) =
  output-stable e v D , λ l Xl off → noOff l Xl (output-offers e v D C off)

-------------------------------------------------------------------------------------
-- Failures of an output node:  { ([] , refusing) } ∪ { (e!v)∷s : failure of the body }.
-------------------------------------------------------------------------------------

output-failures→ : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C : PTree E (ExtI E) R)
                   {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                 → failures (Output e v C) s X
                 → ((s ≡ []) × Refuses (Output e v C) X)
                 ⊎ (Σ[ t ∈ List (Event√ R) ]
                      (s ≡ evl (evLabel A e v) ∷ t × failures C t X))
output-failures→ e v C (W , pw , ref) with output-⟹-inv e v C pw
... | inj₁ (refl , refl)      = inj₁ (refl , ref)
... | inj₂ (t , refl , reach) = inj₂ (t , refl , (W , reach , ref))

output-failures-nil : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C : PTree E (ExtI E) R)
                      {X : Event√ R → Set ℓx}
                    → Refuses (Output e v C) X → failures (Output e v C) [] X
output-failures-nil e v C ref = Output e v C , ⟹-refl , ref

output-failures-cons : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C : PTree E (ExtI E) R)
                       {t : List (Event√ R)} {X : Event√ R → Set ℓx}
                     → failures C t X
                     → failures (Output e v C) (evl (evLabel A e v) ∷ t) X
output-failures-cons {A = A} e v C (W , reach , ref) =
  W , ⟹-ev (sVis {at = A , e} {a = v} refl (oc-just e v C)) reach , ref

-------------------------------------------------------------------------------------
-- Divergences of an output node:  { (e!v)∷s : divergence of the body }  (the node
-- itself is stable, so it never diverges at the empty trace).
-------------------------------------------------------------------------------------

output-div→ : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C : PTree E (ExtI E) R)
              {s : List (Event√ R)}
            → divergences (Output e v C) s
            → Σ[ t ∈ List (Event√ R) ]
                (s ≡ evl (evLabel A e v) ∷ t × divergences C t)
output-div→ e v C d with output-⟹-inv e v C (d .IsDivergence.reach)
... | inj₁ (eqW , _) =
        ⊥-elim (stable-no-τ (output-stable e v C)
                  (subst Diverges eqW (d .IsDivergence.divwit) .Diverges.step))
... | inj₂ (t , eqOut , reach) =
        t ++ d .IsDivergence.suffix
          , trans (d .IsDivergence.split) (cong (_++ d .IsDivergence.suffix) eqOut)
          , record { prefix  = t                   ; suffix = d .IsDivergence.suffix
                   ; split   = refl                ; witness = d .IsDivergence.witness
                   ; reach   = reach               ; divwit  = d .IsDivergence.divwit }

output-div-cons : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C : PTree E (ExtI E) R)
                  {t : List (Event√ R)}
                → divergences C t
                → divergences (Output e v C) (evl (evLabel A e v) ∷ t)
output-div-cons {A = A} e v C d = record
  { prefix  = evl (evLabel A e v) ∷ d .IsDivergence.prefix
  ; suffix  = d .IsDivergence.suffix
  ; split   = cong (evl (evLabel A e v) ∷_) (d .IsDivergence.split)
  ; witness = d .IsDivergence.witness
  ; reach   = ⟹-ev (sVis {at = A , e} {a = v} refl (oc-just e v C))
                    (d .IsDivergence.reach)
  ; divwit  = d .IsDivergence.divwit }

-------------------------------------------------------------------------------------
-- Lift the two decompositions to failures⊥.
-------------------------------------------------------------------------------------

output-failures⊥→ : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C : PTree E (ExtI E) R)
                    {s : List (Event√ R)} {B : Event√ R → Set ℓr}
                  → failures⊥ (Output e v C) s B
                  → ((s ≡ []) × Refuses (Output e v C) B)
                  ⊎ (Σ[ t ∈ List (Event√ R) ]
                       (s ≡ evl (evLabel A e v) ∷ t × failures⊥ C t B))
output-failures⊥→ e v C (inj₁ f) with output-failures→ e v C f
... | inj₁ (eqs , ref)      = inj₁ (eqs , ref)
... | inj₂ (t , eqs , fC)   = inj₂ (t , eqs , inj₁ fC)
output-failures⊥→ e v C (inj₂ d) with output-div→ e v C d
... | (t , eqs , dC)        = inj₂ (t , eqs , inj₂ dC)

output-failures⊥-nil : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C : PTree E (ExtI E) R)
                       {B : Event√ R → Set ℓr}
                     → Refuses (Output e v C) B → failures⊥ (Output e v C) [] B
output-failures⊥-nil e v C ref = inj₁ (output-failures-nil e v C ref)

output-failures⊥-cons : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (C : PTree E (ExtI E) R)
                        {t : List (Event√ R)} {B : Event√ R → Set ℓr}
                      → failures⊥ C t B
                      → failures⊥ (Output e v C) (evl (evLabel A e v) ∷ t) B
output-failures⊥-cons e v C (inj₁ fC) = inj₁ (output-failures-cons e v C fC)
output-failures⊥-cons e v C (inj₂ dC) = inj₂ (output-div-cons e v C dC)

-------------------------------------------------------------------------------------
-- PART 3 : the output-prefix precongruence.
-------------------------------------------------------------------------------------

-- HEADLINE: the output prefix `e ! v ⟶ ·` is a ⊑FD-PRECONGRUENCE in its continuation —
-- the analogue of `⟶₀-mono-⊑FD` for the single-value offer map, unconditionally
Output-mono-⊑FD : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) {P Q : PTree E (ExtI E) R}
                → P ⊑FD Q → (e ! v ⟶ P) ⊑FD (e ! v ⟶ Q)
Output-mono-⊑FD e v {P} {Q} (Q⊇F⊥ , Q⊇D) = F⊥-part , D-part
  where
    F⊥-part : (Output e v P) ⊇F⊥ (Output e v Q)
    F⊥-part fQ with output-failures⊥→ e v Q fQ
    ... | inj₁ (refl , ref)     =
            output-failures⊥-nil e v P (output-refuses e v Q P ref)
    ... | inj₂ (t , refl , fbQ) =
            output-failures⊥-cons e v P (Q⊇F⊥ fbQ)

    D-part : (Output e v P) ⊇D (Output e v Q)
    D-part dQ with output-div→ e v Q dQ
    ... | (t , refl , dQt) = output-div-cons e v P (Q⊇D dQt)
