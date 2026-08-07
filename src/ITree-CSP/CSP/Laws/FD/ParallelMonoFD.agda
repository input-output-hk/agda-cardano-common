{-# OPTIONS --guardedness #-}

-- Parallel FD-monotonicity: `Par` is ⊑FD-monotone in BOTH operands
-- (`Par-mono-⊑FD`), with the CSP corollaries `∥-mono-⊑FD` / `⦀-mono-⊑FD`, and the
-- replicated-interleaving folds `⦀Fin-mono-⊑FD` / `⦀⋆-mono-⊑FD` (Layer 8) and the
-- replicated INTERFACE-parallel folds `∥⁺-mono-⊑FD` / `∥Fin-mono-⊑FD` (Layer 9).
--
-- Layer 10 adds the STABLE-FAILURES analogues `Par-mono-⊑F` + all six folds
-- (`∥-mono-⊑F`, `⦀-mono-⊑F`, `⦀Fin-mono-⊑F`, `⦀⋆-mono-⊑F`, `∥⁺-mono-⊑F`, `∥Fin-mono-⊑F`),
-- which need NO divergence layer at all — see that layer's header.
--
-- All of these are FACT-SHAPED (`⊑FD → ⊑FD`): they are true PRECONGRUENCES, consuming
-- `⊑FD` facts from any source and composing freely — as opposed to a `FSim → ⊑FD`
-- cash-out wrapper, which is a one-liner over the corresponding `*-fsim` and can never
-- consume a `⊑FD` fact.  See `CSP.Laws.FD.IChoiceMonoFD`'s header for the full
-- three-shape taxonomy.
--
-- Proof architecture (classical, via CSP.Laws.FD.FDTransfer's `FD→trace⊥` bridge):
--   • ⊑D half : decompose a target divergence with `Par-reach-div`, push the diverging
--     operand through its `⊑D` hypothesis and the other operand through `FD→trace⊥`;
--     the resulting (shorter) operand prefixes are re-interleaved after TRUNCATING the
--     `ParInter` witness (`ParInter-truncL/R/2`), then extended back to the full trace
--     by `div-extension-closed`.
--   • ⊑F⊥ half : decompose a target stable failure with `Par-failures-elim`; classify
--     the stable composite's operands (`Par-stable-normal`: stable|stable, ret|stable,
--     stable|ret — never ret|ret); CARVE the composite ban set X into per-operand ban
--     sets at level ℓr via the `ParRef` routing (`routeL`/`routeR`); transfer each
--     operand through its `⊑F⊥` hypothesis (`op-transfer-stable` / `op-transfer-ret`,
--     the latter via the √-extension trick of FDTransfer); recombine with
--     `Par-failures-intro` + `route-rebuild`, or fall into the divergence case.
-- No new postulates; all classical strength is inherited from the FIXED interfaces
-- (offer-LEM, Par-Diverges→, Diverges-LEM — each certified in ClassicalFromLEM).

open import Level using (Level; _⊔_; Lift; lift; lower) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
  renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc; ∷-injective; ++-conicalˡ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FD.ParallelMonoFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS      {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures; _⊑F_; ⊑F-refl)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Offers; Refuses)
open import Semantics.DRBisim  {E = E} {I = ExtI E} using (Diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊑F⊥_; _⊑D_; _⊑FD_; failures⊥; divergences; IsDivergence; div-extension-closed;
         ⊑FD-refl)
open import CSP.Laws.FD.FDTransfer E-≟
  using (FD→trace⊥; ⟹-split; term→√failure; √-run-split-gen; div-√-truncate)
open import CSP.Laws.FD.ParallelDivergence E-≟ using (Par-reach-div; Par-div-intro)
open import CSP.Laws.FD.ParallelFailures   E-≟ using (Par-failures-elim; Par-failures-intro)
open import CSP.Laws.FD.ParallelRefusals   E-≟
  using (MaxRef; ParRef; Par-stable; Par-stable-termL; Par-stable-termR;
         mk-stable; stable-not-ret; ret-no-vis-offer)
-- generic stability facts, kept qualified (the two local names below are aliases
-- in the historic argument order)
import Semantics.Stability {E = E} {I = ExtI E} as S
open import CSP.Laws.Traces.TraceLawsParallel E-≟
  using (Mg; fPar-rs; fPar-sr; fPar-re; fPar-er; fPar-nn;
         par-hTauL-eq; par-hTauR-eq; par-pTau-tag0-eq; par-pTau-tag1-eq)
open import CSP.Laws.Traces.TraceLawsParallelElim  E-≟ using (fPar-rr)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√)
open IsDivergence

-- NOTE: all carriers are pinned to ONE common level ℓr (R₁ R₂ R : Set ℓr), forced by
-- `_⊑F⊥_` pinning ban sets to `Set ℓr`; each signature quantifies the carriers
-- EXPLICITLY (generalizable variables would give R₁/R₂/R private level copies).
private
  variable
    ℓr ℓx ℓy ℓx′ ℓy′ : Level

-------------------------------------------------------------------------------------
-- Layer 1 : ParInter TRUNCATIONS.  Stop a `ParInter` interleaving witness once a
-- designated prefix of one (or either) operand trace is fully consumed; the other
-- trace and the composite trace split accordingly.  Structural on the witness; the
-- designated prefix is threaded as an explicit list + a `≡`-constraint (robust
-- against the stuck `p√` index unification).
-------------------------------------------------------------------------------------

-- truncate at the LEFT designated prefix `p` (the right side keeps draining psoloR's)
ParInter-truncL : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                  (p : List (Event√ R₁)) {pr : List (Event√ R₁)}
                  {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
                → sP ≡ p ++ pr
                → ParInter A merge sP sQ s
                → Σ[ q₀ ∈ List (Event√ R₂) ] Σ[ q₁ ∈ List (Event√ R₂) ]
                  Σ[ s₀ ∈ List (Event√ R) ] Σ[ s₁ ∈ List (Event√ R) ]
                    (ParInter A merge p q₀ s₀ × (sQ ≡ q₀ ++ q₁) × (s ≡ s₀ ++ s₁))
ParInter-truncL A merge [] {pr} {sP} {sQ} {s} eq w = [] , sQ , [] , s , pnil , refl , refl
ParInter-truncL A merge (e ∷ p′) () pnil
ParInter-truncL A merge (e ∷ p′) eq (psync m w) with ∷-injective eq
... | refl , teq with ParInter-truncL A merge p′ teq w
...   | q₀ , q₁ , s₀ , s₁ , i₀ , qeq , seq =
        _ ∷ q₀ , q₁ , _ ∷ s₀ , s₁ , psync m i₀ , cong (_ ∷_) qeq , cong (_ ∷_) seq
ParInter-truncL A merge (e ∷ p′) eq (psoloL m w) with ∷-injective eq
... | refl , teq with ParInter-truncL A merge p′ teq w
...   | q₀ , q₁ , s₀ , s₁ , i₀ , qeq , seq =
        q₀ , q₁ , _ ∷ s₀ , s₁ , psoloL m i₀ , qeq , cong (_ ∷_) seq
ParInter-truncL A merge (e ∷ p′) eq (psoloR m w) with ParInter-truncL A merge (e ∷ p′) eq w
... | q₀ , q₁ , s₀ , s₁ , i₀ , qeq , seq =
        _ ∷ q₀ , q₁ , _ ∷ s₀ , s₁ , psoloR m i₀ , cong (_ ∷_) qeq , cong (_ ∷_) seq
ParInter-truncL A merge (e ∷ p′) {pr} eq (p√ {r₁ = r₁} {r₂ = r₂}) with ∷-injective eq
... | refl , teq with ++-conicalˡ p′ pr (sym teq)
...   | refl = √ r₂ ∷ [] , [] , √ (merge r₁ r₂) ∷ [] , [] , p√ , refl , refl

-- truncate at the RIGHT designated prefix `q` (mirror of ParInter-truncL)
ParInter-truncR : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                  (q : List (Event√ R₂)) {qr : List (Event√ R₂)}
                  {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
                → sQ ≡ q ++ qr
                → ParInter A merge sP sQ s
                → Σ[ p₀ ∈ List (Event√ R₁) ] Σ[ p₁ ∈ List (Event√ R₁) ]
                  Σ[ s₀ ∈ List (Event√ R) ] Σ[ s₁ ∈ List (Event√ R) ]
                    (ParInter A merge p₀ q s₀ × (sP ≡ p₀ ++ p₁) × (s ≡ s₀ ++ s₁))
ParInter-truncR A merge [] {qr} {sP} {sQ} {s} eq w = [] , sP , [] , s , pnil , refl , refl
ParInter-truncR A merge (e ∷ q′) () pnil
ParInter-truncR A merge (e ∷ q′) eq (psync m w) with ∷-injective eq
... | refl , teq with ParInter-truncR A merge q′ teq w
...   | p₀ , p₁ , s₀ , s₁ , i₀ , peq , seq =
        _ ∷ p₀ , p₁ , _ ∷ s₀ , s₁ , psync m i₀ , cong (_ ∷_) peq , cong (_ ∷_) seq
ParInter-truncR A merge (e ∷ q′) eq (psoloL m w) with ParInter-truncR A merge (e ∷ q′) eq w
... | p₀ , p₁ , s₀ , s₁ , i₀ , peq , seq =
        _ ∷ p₀ , p₁ , _ ∷ s₀ , s₁ , psoloL m i₀ , cong (_ ∷_) peq , cong (_ ∷_) seq
ParInter-truncR A merge (e ∷ q′) eq (psoloR m w) with ∷-injective eq
... | refl , teq with ParInter-truncR A merge q′ teq w
...   | p₀ , p₁ , s₀ , s₁ , i₀ , peq , seq =
        p₀ , p₁ , _ ∷ s₀ , s₁ , psoloR m i₀ , peq , cong (_ ∷_) seq
ParInter-truncR A merge (e ∷ q′) {qr} eq (p√ {r₁ = r₁} {r₂ = r₂}) with ∷-injective eq
... | refl , teq with ++-conicalˡ q′ qr (sym teq)
...   | refl = √ r₁ ∷ [] , [] , √ (merge r₁ r₂) ∷ [] , [] , p√ , refl , refl

-- truncate at WHICHEVER designated prefix (`p` left / `q` right) completes first
ParInter-trunc2 : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                  (p : List (Event√ R₁)) (q : List (Event√ R₂))
                  {prP : List (Event√ R₁)} {prQ : List (Event√ R₂)}
                  {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
                → sP ≡ p ++ prP → sQ ≡ q ++ prQ
                → ParInter A merge sP sQ s
                → (Σ[ q₀ ∈ List (Event√ R₂) ] Σ[ q₁ ∈ List (Event√ R₂) ]
                   Σ[ s₀ ∈ List (Event√ R) ] Σ[ s₁ ∈ List (Event√ R) ]
                     (ParInter A merge p q₀ s₀ × (q ≡ q₀ ++ q₁) × (s ≡ s₀ ++ s₁)))
                ⊎ (Σ[ p₀ ∈ List (Event√ R₁) ] Σ[ p₁ ∈ List (Event√ R₁) ]
                   Σ[ s₀ ∈ List (Event√ R) ] Σ[ s₁ ∈ List (Event√ R) ]
                     (ParInter A merge p₀ q s₀ × (p ≡ p₀ ++ p₁) × (s ≡ s₀ ++ s₁)))
ParInter-trunc2 A merge [] q {s = s} eqP eqQ w = inj₁ ([] , q , [] , s , pnil , refl , refl)
ParInter-trunc2 A merge (e ∷ p′) [] {s = s} eqP eqQ w =
  inj₂ ([] , e ∷ p′ , [] , s , pnil , refl , refl)
ParInter-trunc2 A merge (e ∷ p′) (f ∷ q′) () eqQ pnil
ParInter-trunc2 A merge (e ∷ p′) (f ∷ q′) eqP eqQ (psync m w)
  with ∷-injective eqP | ∷-injective eqQ
... | refl , teP | feq , teQ with feq
...   | refl with ParInter-trunc2 A merge p′ q′ teP teQ w
...     | inj₁ (q₀ , q₁ , s₀ , s₁ , i₀ , qeq , seq) =
          inj₁ (_ ∷ q₀ , q₁ , _ ∷ s₀ , s₁ , psync m i₀ , cong (_ ∷_) qeq , cong (_ ∷_) seq)
...     | inj₂ (p₀ , p₁ , s₀ , s₁ , i₀ , peq , seq) =
          inj₂ (_ ∷ p₀ , p₁ , _ ∷ s₀ , s₁ , psync m i₀ , cong (_ ∷_) peq , cong (_ ∷_) seq)
ParInter-trunc2 A merge (e ∷ p′) (f ∷ q′) eqP eqQ (psoloL m w) with ∷-injective eqP
... | refl , teP with ParInter-trunc2 A merge p′ (f ∷ q′) teP eqQ w
...   | inj₁ (q₀ , q₁ , s₀ , s₁ , i₀ , qeq , seq) =
        inj₁ (q₀ , q₁ , _ ∷ s₀ , s₁ , psoloL m i₀ , qeq , cong (_ ∷_) seq)
...   | inj₂ (p₀ , p₁ , s₀ , s₁ , i₀ , peq , seq) =
        inj₂ (_ ∷ p₀ , p₁ , _ ∷ s₀ , s₁ , psoloL m i₀ , cong (_ ∷_) peq , cong (_ ∷_) seq)
ParInter-trunc2 A merge (e ∷ p′) (f ∷ q′) eqP eqQ (psoloR m w) with ∷-injective eqQ
... | refl , teQ with ParInter-trunc2 A merge (e ∷ p′) q′ eqP teQ w
...   | inj₁ (q₀ , q₁ , s₀ , s₁ , i₀ , qeq , seq) =
        inj₁ (_ ∷ q₀ , q₁ , _ ∷ s₀ , s₁ , psoloR m i₀ , cong (_ ∷_) qeq , cong (_ ∷_) seq)
...   | inj₂ (p₀ , p₁ , s₀ , s₁ , i₀ , peq , seq) =
        inj₂ (p₀ , p₁ , _ ∷ s₀ , s₁ , psoloR m i₀ , peq , cong (_ ∷_) seq)
ParInter-trunc2 A merge (e ∷ p′) (f ∷ q′) {prP} {prQ} eqP eqQ (p√ {r₁ = r₁} {r₂ = r₂})
  with ∷-injective eqP | ∷-injective eqQ
... | refl , teP | feq , teQ with feq
...   | refl with ++-conicalˡ p′ prP (sym teP) | ++-conicalˡ q′ prQ (sym teQ)
...     | refl | refl =
          inj₁ (√ r₂ ∷ [] , [] , √ (merge r₁ r₂) ∷ [] , [] , p√ , refl , refl)

-------------------------------------------------------------------------------------
-- Layer 2 : STABILITY / NORMALITY plumbing.  A stable `Par P* Q*` forces each operand
-- into a normal form: both stable, ret|stable, or stable|ret (never ret|ret, never a
-- sil on either side — those all make the composite ret/sil/τ-enabled).
-------------------------------------------------------------------------------------

-- a state whose force is sil is not stable (mirror of ParallelRefusals.stable-not-ret;
-- an alias for `Semantics.Stability.stable-not-sil`, whose arguments are the other way)
stable-not-sil : ∀ {ℓr} {R : Set ℓr} {t u : PTree E (ExtI E) R}
               → PTree.force t ≡ sil u → isStable t → ⊥
stable-not-sil {t = t} eqf st = S.stable-not-sil {t = t} st eqf

-- a stable state forcing to `react v τc` has its τ-branch everywhere nothing
-- (an alias for `Semantics.Stability.stable-react-τc`)
stable-τc≡nothing : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
                    {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  → PTree.force t ≡ react v τc → isStable t
                  → ∀ i a → τc i a ≡ nothing
stable-τc≡nothing {t = t} eqf st = S.stable-react-τc {t = t} st eqf

-- which normal form each operand of a stable Par is in (both-ret is impossible)
ParNormal : ∀ {ℓr} {R₁ R₂ : Set ℓr} (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂) → Set _
ParNormal {R₁ = R₁} {R₂ = R₂} P* Q* =
    (isStable P* × isStable Q*)
  ⊎ (Σ[ r₁ ∈ R₁ ] ((PTree.force P* ≡ ret r₁) × isStable Q*))
  ⊎ (isStable P* × Σ[ r₂ ∈ R₂ ] (PTree.force Q* ≡ ret r₂))

-- invert composite stability into the operand normal forms (the elim of Par-stable /
-- Par-stable-termL/R): case on the operands' forces via the inspect-style `go`,
-- discharging the sil / ret|ret shapes and projecting the composite's everywhere-
-- nothing τ-map back onto the operands' own τ-maps.
Par-stable-normal : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                    (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂)
                  → isStable (Par A merge P* Q*) → ParNormal P* Q*
Par-stable-normal {R₁ = R₁} {R₂ = R₂} {R = R} A merge P* Q* st =
    go (PTree.force P*) refl (PTree.force Q*) refl
  where
  go : (nP : NodeKind E (ExtI E) R₁) → PTree.force P* ≡ nP
     → (nQ : NodeKind E (ExtI E) R₂) → PTree.force Q* ≡ nQ
     → ParNormal P* Q*
  -- ret|ret : the composite is ret — not stable
  go (ret r₁) eqP (ret r₂) eqQ =
    ⊥-elim (stable-not-ret {t = Par A merge P* Q*} (fPar-rr A merge eqP eqQ) st)
  -- a sil paired with ret : the composite is sil — not stable
  go (ret r₁) eqP (sil Q′) eqQ =
    ⊥-elim (stable-not-sil {t = Par A merge P* Q*} (fPar-rs A merge eqP eqQ) st)
  go (sil P′) eqP (ret r₂) eqQ =
    ⊥-elim (stable-not-sil {t = Par A merge P* Q*} (fPar-sr A merge eqP eqQ) st)
  -- ret|react : composite τ-map is par-hTauR; project it back onto τcQ
  go (ret r₁) eqP (react vQ τcQ) eqQ =
      inj₂ (inj₁ (r₁ , eqP , mk-stable {t = Q*} eqQ τcQ-nothing))
    where
    hC : ∀ i a → par-hTauR A merge P* τcQ i a ≡ nothing
    hC = stable-τc≡nothing {t = Par A merge P* Q*} (fPar-re A merge eqP eqQ) st
    τcQ-nothing : ∀ i a → τcQ i a ≡ nothing
    τcQ-nothing i a with τcQ i a in tq
    ... | nothing = refl
    ... | just Q′ =
          case trans (sym (par-hTauR-eq A merge P* {τcQ = τcQ} {i = i} {a = a} tq)) (hC i a)
          of λ ()
  -- react|ret : mirror via par-hTauL
  go (react vP τcP) eqP (ret r₂) eqQ =
      inj₂ (inj₂ (mk-stable {t = P*} eqP τcP-nothing , r₂ , eqQ))
    where
    hC : ∀ i a → par-hTauL A merge τcP Q* i a ≡ nothing
    hC = stable-τc≡nothing {t = Par A merge P* Q*} (fPar-er A merge eqP eqQ) st
    τcP-nothing : ∀ i a → τcP i a ≡ nothing
    τcP-nothing i a with τcP i a in tp
    ... | nothing = refl
    ... | just P′ =
          case trans (sym (par-hTauL-eq A merge {τcP = τcP} Q* {i = i} {a = a} tp)) (hC i a)
          of λ ()
  -- a sil operand in the general react|react node : its oneτ shows at tag0/tag1 — absurd
  go (sil P′) eqP (sil Q′) eqQ =
    ⊥-elim (case trans
        (sym (par-pTau-tag0-eq A merge (sil P′) (sil Q′) P* Q*
                {iₚ = (Lift ℓ (Fin 1) , fin)} {aₚ = lift fzero} refl))
        (stable-τc≡nothing {t = Par A merge P* Q*} (fPar-nn A merge eqP eqQ tt₀ tt₀) st
          ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero))
      of λ ())
  go (sil P′) eqP (react vQ τcQ) eqQ =
    ⊥-elim (case trans
        (sym (par-pTau-tag0-eq A merge (sil P′) (react vQ τcQ) P* Q*
                {iₚ = (Lift ℓ (Fin 1) , fin)} {aₚ = lift fzero} refl))
        (stable-τc≡nothing {t = Par A merge P* Q*} (fPar-nn A merge eqP eqQ tt₀ tt₀) st
          ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero))
      of λ ())
  go (react vP τcP) eqP (sil Q′) eqQ =
    ⊥-elim (case trans
        (sym (par-pTau-tag1-eq A merge (react vP τcP) (sil Q′) P* Q*
                {iₚ = (Lift ℓ (Fin 1) , fin)} {aₚ = lift fzero} refl))
        (stable-τc≡nothing {t = Par A merge P* Q*} (fPar-nn A merge eqP eqQ tt₀ tt₀) st
          ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift (fsuc fzero) , lift fzero))
      of λ ())
  -- react|react : project the composite's par-pTau at tag0 / tag1 back onto τcP / τcQ
  go (react vP τcP) eqP (react vQ τcQ) eqQ =
      inj₁ (mk-stable {t = P*} eqP τcP-nothing , mk-stable {t = Q*} eqQ τcQ-nothing)
    where
    hC : ∀ i a → par-pTau A merge (react vP τcP) (react vQ τcQ) P* Q* i a ≡ nothing
    hC = stable-τc≡nothing {t = Par A merge P* Q*} (fPar-nn A merge eqP eqQ tt₀ tt₀) st
    τcP-nothing : ∀ i a → τcP i a ≡ nothing
    τcP-nothing j b with τcP j b in tp
    ... | nothing = refl
    ... | just P′ =
          case trans
            (sym (par-pTau-tag0-eq A merge (react vP τcP) (react vQ τcQ) P* Q*
                    {iₚ = j} {aₚ = b} tp))
            (hC ((Lift ℓ (Fin 2) × proj₁ j) , pair fin (proj₂ j)) (lift fzero , b))
          of λ ()
    τcQ-nothing : ∀ i a → τcQ i a ≡ nothing
    τcQ-nothing j b with τcQ j b in tq
    ... | nothing = refl
    ... | just Q′ =
          case trans
            (sym (par-pTau-tag1-eq A merge (react vP τcP) (react vQ τcQ) P* Q*
                    {iₚ = j} {aₚ = b} tq))
            (hC ((Lift ℓ (Fin 2) × proj₁ j) , pair fin (proj₂ j)) (lift (fsuc fzero) , b))
          of λ ()

-------------------------------------------------------------------------------------
-- Layer 3 : BAN-SET ROUTING.  Carve a composite refusal `X : Event√ R → Set ℓr` into
-- per-operand ban sets AT THE SAME LEVEL ℓr, following the routing that a given
-- `ParRef A X XP XQ` certificate performs (its cs-clause is a routing function; the
-- Set₀ tags `IsInj₁`/`IsInj₂` record which way it routed without raising the level).
-------------------------------------------------------------------------------------

-- Set₀ tag for a sum value that took the LEFT injection
IsInj₁ : ∀ {la lb} {A : Set la} {B : Set lb} → A ⊎ B → Set
IsInj₁ (inj₁ _) = ⊤₀
IsInj₁ (inj₂ _) = ⊥

-- Set₀ tag for a sum value that took the RIGHT injection
IsInj₂ : ∀ {la lb} {A : Set la} {B : Set lb} → A ⊎ B → Set
IsInj₂ (inj₁ _) = ⊥
IsInj₂ (inj₂ _) = ⊤₀

-- dec-indexed body of the LEFT route (kept as a plain function of the Dec value so
-- the coverage/rebuild lemmas can align with it definitionally, never re-`with`ing)
routeLd : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
          (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
        → ParRef A X XP XQ
        → {Y : Set ℓ} {f : E Y} {a : Y} → Dec (A .mem (Y , f) a) → Set ℓr
routeLd A X XP XQ (csCl , _) {Y} {f} {a} (yes m) =
  Σ[ xe ∈ X (evl (evLabel Y f a)) ] IsInj₁ (csCl f a m xe)
routeLd A X XP XQ _          {Y} {f} {a} (no _)  = X (evl (evLabel Y f a))

-- dec-indexed body of the RIGHT route (mirror; IsInj₂ of the same cs-routing)
routeRd : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
          (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
        → ParRef A X XP XQ
        → {Y : Set ℓ} {f : E Y} {a : Y} → Dec (A .mem (Y , f) a) → Set ℓr
routeRd A X XP XQ (csCl , _) {Y} {f} {a} (yes m) =
  Σ[ xe ∈ X (evl (evLabel Y f a)) ] IsInj₂ (csCl f a m xe)
routeRd A X XP XQ _          {Y} {f} {a} (no _)  = X (evl (evLabel Y f a))

-- the P-side share of the composite ban set X under a ParRef route (√ never banned)
routeL : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
         (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
       → ParRef A X XP XQ → Event√ R₁ → Set ℓr
routeL A X XP XQ pr (evl (evLabel Y f a)) = routeLd A X XP XQ pr (A .dec (Y , f) a)
routeL {ℓr = ℓr} A X XP XQ pr (√ _) = Lift ℓr ⊥

-- the Q-side share of the composite ban set X under a ParRef route (√ never banned)
routeR : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
         (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
       → ParRef A X XP XQ → Event√ R₂ → Set ℓr
routeR A X XP XQ pr (evl (evLabel Y f a)) = routeRd A X XP XQ pr (A .dec (Y , f) a)
routeR {ℓr = ℓr} A X XP XQ pr (√ _) = Lift ℓr ⊥

-- dec-indexed coverage: a routed-left event is in the route's left target XP
routeLd-covers : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
                 (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
                 (pr : ParRef A X XP XQ)
                 {Y : Set ℓ} {f : E Y} {a : Y} (d : Dec (A .mem (Y , f) a))
               → routeLd A X XP XQ pr d → XP (evl (evLabel Y f a))
routeLd-covers A X XP XQ (csCl , ncsCl) {Y} {f} {a} (yes m) (xe , tag) with csCl f a m xe
... | inj₁ xp = xp
... | inj₂ _  = ⊥-elim tag
routeLd-covers A X XP XQ (csCl , ncsCl) {Y} {f} {a} (no ¬m) xe = proj₁ (ncsCl f a ¬m xe)

-- dec-indexed coverage: a routed-right event is in the route's right target XQ
routeRd-covers : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
                 (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
                 (pr : ParRef A X XP XQ)
                 {Y : Set ℓ} {f : E Y} {a : Y} (d : Dec (A .mem (Y , f) a))
               → routeRd A X XP XQ pr d → XQ (evl (evLabel Y f a))
routeRd-covers A X XP XQ (csCl , ncsCl) {Y} {f} {a} (yes m) (xe , tag) with csCl f a m xe
... | inj₁ _  = ⊥-elim tag
... | inj₂ xq = xq
routeRd-covers A X XP XQ (csCl , ncsCl) {Y} {f} {a} (no ¬m) xe = proj₂ (ncsCl f a ¬m xe)

-- the left route's target IS the source XP: membership is refused at the source
routeL-covers : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
                (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
                (pr : ParRef A X XP XQ)
              → ∀ e → routeL A X XP XQ pr e → XP e
routeL-covers A X XP XQ pr (evl (evLabel Y f a)) rl =
  routeLd-covers A X XP XQ pr (A .dec (Y , f) a) rl
routeL-covers A X XP XQ pr (√ x) rl = ⊥-elim (lower rl)

-- the right route's target IS the source XQ: membership is refused at the source
routeR-covers : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
                (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
                (pr : ParRef A X XP XQ)
              → ∀ e → routeR A X XP XQ pr e → XQ e
routeR-covers A X XP XQ pr (evl (evLabel Y f a)) rl =
  routeRd-covers A X XP XQ pr (A .dec (Y , f) a) rl
routeR-covers A X XP XQ pr (√ x) rl = ⊥-elim (lower rl)

-- rebuild a ParRef on TARGET residual predicates from per-side coverage of the routes
route-rebuild : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
                (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
                (pr : ParRef A X XP XQ)
                {XP′ : Event√ R₁ → Set ℓx′} {XQ′ : Event√ R₂ → Set ℓy′}
              → (∀ e → routeL A X XP XQ pr e → XP′ e)
              → (∀ e → routeR A X XP XQ pr e → XQ′ e)
              → ParRef A X XP′ XQ′
route-rebuild A X XP XQ pr {XP′ = XP′} {XQ′ = XQ′} cL cR = csCl′ , ncsCl′
  where
  csCl′ : ∀ {Y} (f : E Y) (a : Y) → A .mem (Y , f) a → X (evl (evLabel Y f a))
        → XP′ (evl (evLabel Y f a)) ⊎ XQ′ (evl (evLabel Y f a))
  csCl′ {Y} f a m′ xe with A .dec (Y , f) a in deq
  ... | no ¬m = ⊥-elim (¬m m′)
  ... | yes m with proj₁ pr f a m xe in ceq
  ...   | inj₁ _ = inj₁ (cL (evl (evLabel Y f a))
                    (subst (λ d → routeLd A X XP XQ pr {Y} {f} {a} d) (sym deq)
                           (xe , subst IsInj₁ (sym ceq) tt₀)))
  ...   | inj₂ _ = inj₂ (cR (evl (evLabel Y f a))
                    (subst (λ d → routeRd A X XP XQ pr {Y} {f} {a} d) (sym deq)
                           (xe , subst IsInj₂ (sym ceq) tt₀)))
  ncsCl′ : ∀ {Y} (f : E Y) (a : Y) → ¬ A .mem (Y , f) a → X (evl (evLabel Y f a))
         → XP′ (evl (evLabel Y f a)) × XQ′ (evl (evLabel Y f a))
  ncsCl′ {Y} f a ¬m′ xe with A .dec (Y , f) a in deq
  ... | yes m = ⊥-elim (¬m′ m)
  ... | no ¬m =
        cL (evl (evLabel Y f a)) (subst (λ d → routeLd A X XP XQ pr {Y} {f} {a} d) (sym deq) xe)
      , cR (evl (evLabel Y f a)) (subst (λ d → routeRd A X XP XQ pr {Y} {f} {a} d) (sym deq) xe)

-- a terminated residual maximally covers a route (routes never ban √; ret offers only √)
ret-routeL-cover : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
                   (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
                   (pr : ParRef A X XP XQ)
                   {t : PTree E (ExtI E) R₁} {r : R₁}
                 → PTree.force t ≡ ret r → ∀ e → routeL A X XP XQ pr e → MaxRef t e
ret-routeL-cover A X XP XQ pr {t = t} fe (evl (evLabel Y f a)) b = ret-no-vis-offer {t = t} fe
ret-routeL-cover A X XP XQ pr {t = t} fe (√ x) b = ⊥-elim (lower b)

-- mirror: a terminated right residual maximally covers the right route
ret-routeR-cover : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (X : Event√ R → Set ℓr)
                   (XP : Event√ R₁ → Set ℓx) (XQ : Event√ R₂ → Set ℓy)
                   (pr : ParRef A X XP XQ)
                   {t : PTree E (ExtI E) R₂} {r : R₂}
                 → PTree.force t ≡ ret r → ∀ e → routeR A X XP XQ pr e → MaxRef t e
ret-routeR-cover A X XP XQ pr {t = t} fe (evl (evLabel Y f a)) b = ret-no-vis-offer {t = t} fe
ret-routeR-cover A X XP XQ pr {t = t} fe (√ x) b = ⊥-elim (lower b)

-------------------------------------------------------------------------------------
-- Layer 4 : PER-OPERAND TRANSFER through the refinement hypothesis.  A target-side
-- reach to a stable (resp. ret) residual becomes, on the refined side, a same-trace
-- stable failure (resp. a same-trace, same-value termination) or a divergence.
-------------------------------------------------------------------------------------

-- transfer a stable residual: feed ⊑F⊥ the stable failure at the routed ban set
op-transfer-stable : ∀ {ℓr} {R₁ : Set ℓr}
                     {P₁ P₂ P₂* : PTree E (ExtI E) R₁} {sP : List (Event√ R₁)}
                     {BP : Event√ R₁ → Set ℓr}
                   → P₁ ⊑F⊥ P₂
                   → P₂ ⟹⟨ sP ⟩ P₂* → isStable P₂*
                   → (∀ e → BP e → MaxRef P₂* e)
                   → failures P₁ sP BP ⊎ divergences P₁ sP
op-transfer-stable {P₂* = P₂*} {BP = BP} fF run st covers =
  fF {B = BP} (inj₁ (P₂* , run , (st , covers)))

-- transfer a terminated residual: √-extend the run into an empty-ban failure, push it
-- through ⊑F⊥, then split the √ back off (or truncate the √ off the divergence)
op-transfer-ret : ∀ {ℓr} {R₁ : Set ℓr}
                  {P₁ P₂ P₂* : PTree E (ExtI E) R₁} {sP : List (Event√ R₁)} {r : R₁}
                → P₁ ⊑F⊥ P₂
                → P₂ ⟹⟨ sP ⟩ P₂* → PTree.force P₂* ≡ ret r
                → (Σ[ P₁ᵣ ∈ PTree E (ExtI E) R₁ ]
                     ((P₁ ⟹⟨ sP ⟩ P₁ᵣ) × (PTree.force P₁ᵣ ≡ ret r)))
                  ⊎ divergences P₁ sP
op-transfer-ret {ℓr = ℓr} {sP = sP} {r = r} fF run eqret
  with fF {sP ++ √ r ∷ []} {λ _ → Lift ℓr ⊥} (inj₁ (term→√failure run eqret))
... | inj₁ (T , run√ , _) = inj₁ (√-run-split-gen sP run√)
... | inj₂ dv√            = inj₂ (div-√-truncate dv√)

-------------------------------------------------------------------------------------
-- Layer 5 : the ⊑D half.  Re-interleave transferred divergences/runs on the operand
-- prefixes into a composite divergence at a prefix of the original trace, then extend.
-------------------------------------------------------------------------------------

-- package a full-trace reach to a diverging state as an IsDivergence (empty suffix)
mk-full-div : ∀ {ℓr} {R : Set ℓr} {T T* : PTree E (ExtI E) R} {s : List (Event√ R)}
            → T ⟹⟨ s ⟩ T* → Diverges T* → IsDivergence T s
mk-full-div {T* = T*} {s = s} run dv = record
  { prefix = s ; suffix = [] ; split = sym (++-identityʳ s)
  ; witness = T* ; reach = run ; divwit = dv }

-- extend a divergence at a prefix s₀ of pre back to the full trace s ≡ pre ++ suf
div-extend : ∀ {ℓr} {R : Set ℓr} {T : PTree E (ExtI E) R} {pre suf s s₀ s₁ : List (Event√ R)}
           → s ≡ pre ++ suf → pre ≡ s₀ ++ s₁ → divergences T s₀ → divergences T s
div-extend {T = T} {pre} {suf} {s} {s₀} {s₁} spl peq d =
  subst (divergences T)
        (sym (trans spl (trans (cong (_++ suf) peq) (++-assoc s₀ s₁ suf))))
        (div-extension-closed {t = s₁ ++ suf} d)

-- LEFT operand diverges, RIGHT runs the full sub-trace: truncate the interleaving at
-- the left divergence prefix and re-interleave into a composite divergence
Par-div-transfer-L : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                     (P₁ : PTree E (ExtI E) R₁) (Q₁ : PTree E (ExtI E) R₂)
                     {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {pre : List (Event√ R)}
                     {Q₁* : PTree E (ExtI E) R₂}
                   → ParInter A merge sP sQ pre
                   → IsDivergence P₁ sP
                   → Q₁ ⟹⟨ sQ ⟩ Q₁*
                   → Σ[ s₀ ∈ List (Event√ R) ] Σ[ s₁ ∈ List (Event√ R) ]
                       ((pre ≡ s₀ ++ s₁) × divergences (Par A merge P₁ Q₁) s₀)
Par-div-transfer-L A merge P₁ Q₁ {Q₁* = Q₁*} inter dv rQ
  with ParInter-truncL A merge (dv .prefix) (dv .split) inter
... | q₀ , q₁ , s₀ , s₁ , i₀ , qeq , seq
  with ⟹-split q₀ (subst (λ z → Q₁ ⟹⟨ z ⟩ Q₁*) qeq rQ)
...   | m , rQ₀ , _ =
        s₀ , s₁ , seq ,
        Par-div-intro A merge P₁ Q₁ (dv .reach) rQ₀ i₀ (inj₁ (dv .divwit))

-- RIGHT operand diverges, LEFT runs the full sub-trace (mirror)
Par-div-transfer-R : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                     (P₁ : PTree E (ExtI E) R₁) (Q₁ : PTree E (ExtI E) R₂)
                     {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {pre : List (Event√ R)}
                     {P₁* : PTree E (ExtI E) R₁}
                   → ParInter A merge sP sQ pre
                   → IsDivergence Q₁ sQ
                   → P₁ ⟹⟨ sP ⟩ P₁*
                   → Σ[ s₀ ∈ List (Event√ R) ] Σ[ s₁ ∈ List (Event√ R) ]
                       ((pre ≡ s₀ ++ s₁) × divergences (Par A merge P₁ Q₁) s₀)
Par-div-transfer-R A merge P₁ Q₁ {P₁* = P₁*} inter dv rP
  with ParInter-truncR A merge (dv .prefix) (dv .split) inter
... | p₀ , p₁ , s₀ , s₁ , i₀ , peq , seq
  with ⟹-split p₀ (subst (λ z → P₁ ⟹⟨ z ⟩ P₁*) peq rP)
...   | m , rP₀ , _ =
        s₀ , s₁ , seq ,
        Par-div-intro A merge P₁ Q₁ rP₀ (dv .reach) i₀ (inj₂ (dv .divwit))

-- BOTH operands diverge: truncate at whichever divergence prefix completes first
Par-div-transfer-2 : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                     (P₁ : PTree E (ExtI E) R₁) (Q₁ : PTree E (ExtI E) R₂)
                     {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {pre : List (Event√ R)}
                   → ParInter A merge sP sQ pre
                   → IsDivergence P₁ sP
                   → IsDivergence Q₁ sQ
                   → Σ[ s₀ ∈ List (Event√ R) ] Σ[ s₁ ∈ List (Event√ R) ]
                       ((pre ≡ s₀ ++ s₁) × divergences (Par A merge P₁ Q₁) s₀)
Par-div-transfer-2 A merge P₁ Q₁ inter dvP dvQ
  with ParInter-trunc2 A merge (dvP .prefix) (dvQ .prefix) (dvP .split) (dvQ .split) inter
... | inj₁ (q₀ , q₁ , s₀ , s₁ , i₀ , qeq , seq)
  with ⟹-split q₀ (subst (λ z → Q₁ ⟹⟨ z ⟩ (dvQ .witness)) qeq (dvQ .reach))
...   | m , rQ₀ , _ =
        s₀ , s₁ , seq ,
        Par-div-intro A merge P₁ Q₁ (dvP .reach) rQ₀ i₀ (inj₁ (dvP .divwit))
Par-div-transfer-2 A merge P₁ Q₁ inter dvP dvQ
    | inj₂ (p₀ , p₁ , s₀ , s₁ , i₀ , peq , seq)
  with ⟹-split p₀ (subst (λ z → P₁ ⟹⟨ z ⟩ (dvP .witness)) peq (dvP .reach))
...   | m , rP₀ , _ =
        s₀ , s₁ , seq ,
        Par-div-intro A merge P₁ Q₁ rP₀ (dvQ .reach) i₀ (inj₂ (dvQ .divwit))

-- Par-div-transfer-L specialised to a full-trace divergence (suffix = [], pre = s)
Par-div-out-L : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                (P₁ : PTree E (ExtI E) R₁) (Q₁ : PTree E (ExtI E) R₂)
                {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
                {Q₁* : PTree E (ExtI E) R₂}
              → ParInter A merge sP sQ s
              → IsDivergence P₁ sP → Q₁ ⟹⟨ sQ ⟩ Q₁*
              → divergences (Par A merge P₁ Q₁) s
Par-div-out-L A merge P₁ Q₁ {s = s} inter dv rQ
  with Par-div-transfer-L A merge P₁ Q₁ inter dv rQ
... | s₀ , s₁ , peq , d = div-extend (sym (++-identityʳ s)) peq d

-- Par-div-transfer-R specialised to a full-trace divergence (mirror)
Par-div-out-R : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                (P₁ : PTree E (ExtI E) R₁) (Q₁ : PTree E (ExtI E) R₂)
                {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
                {P₁* : PTree E (ExtI E) R₁}
              → ParInter A merge sP sQ s
              → IsDivergence Q₁ sQ → P₁ ⟹⟨ sP ⟩ P₁*
              → divergences (Par A merge P₁ Q₁) s
Par-div-out-R A merge P₁ Q₁ {s = s} inter dv rP
  with Par-div-transfer-R A merge P₁ Q₁ inter dv rP
... | s₀ , s₁ , peq , d = div-extend (sym (++-identityʳ s)) peq d

-- Par-div-transfer-2 specialised to a full-trace divergence
Par-div-out-2 : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                (P₁ : PTree E (ExtI E) R₁) (Q₁ : PTree E (ExtI E) R₂)
                {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
              → ParInter A merge sP sQ s
              → IsDivergence P₁ sP → IsDivergence Q₁ sQ
              → divergences (Par A merge P₁ Q₁) s
Par-div-out-2 A merge P₁ Q₁ {s = s} inter dvP dvQ
  with Par-div-transfer-2 A merge P₁ Q₁ inter dvP dvQ
... | s₀ , s₁ , peq , d = div-extend (sym (++-identityʳ s)) peq d

-- HEADLINE (⊑D half): parallel composition is ⊑D-monotone under ⊑FD hypotheses
Par-mono-⊑D : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
              {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
            → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂
            → (Par A merge P₁ Q₁) ⊑D (Par A merge P₂ Q₂)
Par-mono-⊑D A merge {P₁} {P₂} {Q₁} {Q₂} (fP , dP) (fQ , dQ) {s} d
  with Par-reach-div A merge P₂ Q₂ (d .reach) (d .divwit)
-- left target diverges: transfer it via ⊑D, transfer the right side via FD→trace⊥
... | sP , sQ , P₂* , Q₂* , rP , rQ , inter , inj₁ dvP₂ =
      case FD→trace⊥ fQ dQ rQ of λ where
        (inj₁ (Q₁* , rQ₁)) →
          case Par-div-transfer-L A merge P₁ Q₁ inter (dP (mk-full-div rP dvP₂)) rQ₁ of λ where
            (s₀ , s₁ , peq , dv) → div-extend (d .split) peq dv
        (inj₂ dQ₁) →
          case Par-div-transfer-2 A merge P₁ Q₁ inter (dP (mk-full-div rP dvP₂)) dQ₁ of λ where
            (s₀ , s₁ , peq , dv) → div-extend (d .split) peq dv
-- right target diverges (mirror)
... | sP , sQ , P₂* , Q₂* , rP , rQ , inter , inj₂ dvQ₂ =
      case FD→trace⊥ fP dP rP of λ where
        (inj₁ (P₁* , rP₁)) →
          case Par-div-transfer-R A merge P₁ Q₁ inter (dQ (mk-full-div rQ dvQ₂)) rP₁ of λ where
            (s₀ , s₁ , peq , dv) → div-extend (d .split) peq dv
        (inj₂ dP₁) →
          case Par-div-transfer-2 A merge P₁ Q₁ inter dP₁ (dQ (mk-full-div rQ dvQ₂)) of λ where
            (s₀ , s₁ , peq , dv) → div-extend (d .split) peq dv

-------------------------------------------------------------------------------------
-- Layer 6 : the ⊑F⊥ half.  Decompose the target failure, classify the stable leaf,
-- transfer each operand at its routed ban set, and recombine (or diverge).
-------------------------------------------------------------------------------------

-- recombine the per-operand transfer outcomes of a decomposed target failure
Par-mono-fail : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
                {s : List (Event√ R)} {X : Event√ R → Set ℓr}
                {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)}
                {P₂* : PTree E (ExtI E) R₁} {Q₂* : PTree E (ExtI E) R₂}
              → P₁ ⊑F⊥ P₂ → Q₁ ⊑F⊥ Q₂
              → P₂ ⟹⟨ sP ⟩ P₂* → Q₂ ⟹⟨ sQ ⟩ Q₂*
              → ParInter A merge sP sQ s
              → ParNormal P₂* Q₂*
              → ParRef A X (MaxRef P₂*) (MaxRef Q₂*)
              → failures⊥ (Par A merge P₁ Q₁) s X
-- both operands stable
Par-mono-fail A merge {P₁ = P₁} {Q₁ = Q₁} {X = X} {P₂* = P₂*} {Q₂* = Q₂*}
    fP fQ rP rQ inter (inj₁ (stP , stQ)) pr
  with op-transfer-stable fP rP stP (routeL-covers A X (MaxRef P₂*) (MaxRef Q₂*) pr)
     | op-transfer-stable fQ rQ stQ (routeR-covers A X (MaxRef P₂*) (MaxRef Q₂*) pr)
... | inj₁ (P₁* , rP₁ , refP) | inj₁ (Q₁* , rQ₁ , refQ) =
      inj₁ (Par-failures-intro A merge P₁ Q₁ rP₁ rQ₁ inter
              (Par-stable A merge P₁* Q₁* (proj₁ refP) (proj₁ refQ))
              (route-rebuild A X (MaxRef P₂*) (MaxRef Q₂*) pr (proj₂ refP) (proj₂ refQ)))
... | inj₁ (P₁* , rP₁ , refP) | inj₂ dvQ = inj₂ (Par-div-out-R A merge P₁ Q₁ inter dvQ rP₁)
... | inj₂ dvP | inj₁ (Q₁* , rQ₁ , refQ) = inj₂ (Par-div-out-L A merge P₁ Q₁ inter dvP rQ₁)
... | inj₂ dvP | inj₂ dvQ                = inj₂ (Par-div-out-2 A merge P₁ Q₁ inter dvP dvQ)
-- left operand terminated, right stable
Par-mono-fail A merge {P₁ = P₁} {Q₁ = Q₁} {X = X} {P₂* = P₂*} {Q₂* = Q₂*}
    fP fQ rP rQ inter (inj₂ (inj₁ (r₁ , eqP , stQ))) pr
  with op-transfer-ret fP rP eqP
     | op-transfer-stable fQ rQ stQ (routeR-covers A X (MaxRef P₂*) (MaxRef Q₂*) pr)
... | inj₁ (P₁ᵣ , rP₁ , feP) | inj₁ (Q₁* , rQ₁ , refQ) =
      inj₁ (Par-failures-intro A merge P₁ Q₁ rP₁ rQ₁ inter
              (Par-stable-termL A merge P₁ᵣ Q₁* feP (proj₁ refQ))
              (route-rebuild A X (MaxRef P₂*) (MaxRef Q₂*) pr
                (ret-routeL-cover A X (MaxRef P₂*) (MaxRef Q₂*) pr feP) (proj₂ refQ)))
... | inj₁ (P₁ᵣ , rP₁ , feP) | inj₂ dvQ  = inj₂ (Par-div-out-R A merge P₁ Q₁ inter dvQ rP₁)
... | inj₂ dvP | inj₁ (Q₁* , rQ₁ , refQ) = inj₂ (Par-div-out-L A merge P₁ Q₁ inter dvP rQ₁)
... | inj₂ dvP | inj₂ dvQ                = inj₂ (Par-div-out-2 A merge P₁ Q₁ inter dvP dvQ)
-- left operand stable, right terminated (mirror)
Par-mono-fail A merge {P₁ = P₁} {Q₁ = Q₁} {X = X} {P₂* = P₂*} {Q₂* = Q₂*}
    fP fQ rP rQ inter (inj₂ (inj₂ (stP , r₂ , eqQ))) pr
  with op-transfer-stable fP rP stP (routeL-covers A X (MaxRef P₂*) (MaxRef Q₂*) pr)
     | op-transfer-ret fQ rQ eqQ
... | inj₁ (P₁* , rP₁ , refP) | inj₁ (Q₁ᵣ , rQ₁ , feQ) =
      inj₁ (Par-failures-intro A merge P₁ Q₁ rP₁ rQ₁ inter
              (Par-stable-termR A merge P₁* Q₁ᵣ (proj₁ refP) feQ)
              (route-rebuild A X (MaxRef P₂*) (MaxRef Q₂*) pr
                (proj₂ refP) (ret-routeR-cover A X (MaxRef P₂*) (MaxRef Q₂*) pr feQ)))
... | inj₁ (P₁* , rP₁ , refP) | inj₂ dvQ = inj₂ (Par-div-out-R A merge P₁ Q₁ inter dvQ rP₁)
... | inj₂ dvP | inj₁ (Q₁ᵣ , rQ₁ , feQ)  = inj₂ (Par-div-out-L A merge P₁ Q₁ inter dvP rQ₁)
... | inj₂ dvP | inj₂ dvQ                = inj₂ (Par-div-out-2 A merge P₁ Q₁ inter dvP dvQ)

-- HEADLINE (⊑F⊥ half): parallel composition is ⊑F⊥-monotone under ⊑FD hypotheses
Par-mono-⊑F⊥ : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
               {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
             → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂
             → (Par A merge P₁ Q₁) ⊑F⊥ (Par A merge P₂ Q₂)
Par-mono-⊑F⊥ A merge hP hQ {s} {X} (inj₂ d) = inj₂ (Par-mono-⊑D A merge hP hQ d)
Par-mono-⊑F⊥ A merge {P₁} {P₂} {Q₁} {Q₂} hP hQ {s} {X} (inj₁ f)
  with Par-failures-elim A merge {P = P₂} {Q = Q₂} f
... | sP , sQ , P₂* , Q₂* , rP , rQ , inter , stPar , pr =
      Par-mono-fail A merge (proj₁ hP) (proj₁ hQ) rP rQ inter
                    (Par-stable-normal A merge P₂* Q₂* stPar) pr

-------------------------------------------------------------------------------------
-- Layer 7 : assembly + CSP corollaries.
-------------------------------------------------------------------------------------

-- HEADLINE: parallel composition is ⊑FD-monotone in both operands
Par-mono-⊑FD : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
               {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
             → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂
             → (Par A merge P₁ Q₁) ⊑FD (Par A merge P₂ Q₂)
Par-mono-⊑FD A merge hP hQ = Par-mono-⊑F⊥ A merge hP hQ , Par-mono-⊑D A merge hP hQ

-- CSP interface parallel (⊤-merge) is ⊑FD-monotone
∥-mono-⊑FD : ∀ {ℓr} (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr})}
           → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂ → (P₁ ∥⇘ A ⇙ Q₁) ⊑FD (P₂ ∥⇘ A ⇙ Q₂)
∥-mono-⊑FD A = Par-mono-⊑FD A (λ _ _ → tt)

-- interleaving is ⊑FD-monotone
⦀-mono-⊑FD : ∀ {ℓr} {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr})}
           → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂ → (P₁ ⦀ Q₁) ⊑FD (P₂ ⦀ Q₂)
⦀-mono-⊑FD = Par-mono-⊑FD ∅ES (λ _ _ → tt)

-------------------------------------------------------------------------------------
-- Layer 8 : the REPLICATED-INTERLEAVING folds, FACT-SHAPED.
--
-- Plain inductions over the unconditional `⦀-mono-⊑FD` above, with `⊑FD-refl Skip`
-- (`Semantics.FailuresDivergences`) at the base — `⦀Fin zero f = Skip` and `⦀⋆ [] = Skip`.
--
-- ⚠ NO SIDE CONDITION, BY DESIGN.  The FSim folds `⦀Fin-fsim` / `⦀⋆-fsim`
-- (`CSP.Laws.FSim.ParCongRep`) each demand pairwise-disjoint alphabets (`Disj`) plus
-- `OffersOnly` confinement, purely to discharge `Par-fsim`'s `Sep` obligation at every
-- fold step.  `Par-mono-⊑FD` carries no `Sep`, so the fact-shaped folds below are BOTH
-- simpler and strictly MORE GENERAL: pointwise `⊑FD` is all they ask for.  They
-- therefore take the canonical `-mono-⊑FD` names, and the shape-`FSim → ⊑FD` cash-out
-- wrappers that formerly held those names in `ParCongRep` were retired (write
-- `fsim→⊑FD (⦀Fin-fsim …)` for the witness route; see `CSP.Laws.FD.IChoiceMonoFD`'s
-- header for the three-shape taxonomy and why cash-outs are not worth naming).
-------------------------------------------------------------------------------------

-- `⦀Fin` is ⊑FD-monotone in its `Fin`-indexed family, pointwise and unconditionally
⦀Fin-mono-⊑FD : ∀ {ℓr} {n : ℕ} {f g : Fin n → PTree E (ExtI E) (⊤ {ℓr})}
              → (∀ i → f i ⊑FD g i) → ⦀Fin n f ⊑FD ⦀Fin n g
⦀Fin-mono-⊑FD {n = zero}  h = ⊑FD-refl Skip
⦀Fin-mono-⊑FD {n = suc n} h = ⦀-mono-⊑FD (h fzero) (⦀Fin-mono-⊑FD (λ i → h (fsuc i)))

-- `⦀⋆` is ⊑FD-monotone in its list of operands, pointwise and unconditionally
⦀⋆-mono-⊑FD : ∀ {ℓr} {Ps Qs : List (PTree E (ExtI E) (⊤ {ℓr}))}
            → Pointwise _⊑FD_ Ps Qs → ⦀⋆ Ps ⊑FD ⦀⋆ Qs
⦀⋆-mono-⊑FD []ᵖ       = ⊑FD-refl Skip
⦀⋆-mono-⊑FD (p ∷ᵖ ps) = ⦀-mono-⊑FD p (⦀⋆-mono-⊑FD ps)

-------------------------------------------------------------------------------------
-- Layer 9 : the REPLICATED INTERFACE-PARALLEL folds, FACT-SHAPED.
--
-- These fold `_∥⇘ A ⇙_` (= `Par⊤ A`, one SHARED synchronisation set `A` at every step),
-- not `⦀`, so each carries the `EventSet` as an explicit first argument.
--
-- ⚠ BOTH ARE NON-EMPTY, like `⨅⁺`/`⨅Fin` and unlike Layer 8's `⦀`-folds: `[|A|]` has no
-- unit, so `∥⁺` is head+list (`∥⁺ A P [] = P`, `CSP.Operators`:651) and `∥Fin` is
-- `Fin (suc n)`-indexed (`∥Fin A zero f = f fzero`, `CSP.Operators`:656).  The base case
-- therefore returns an OPERAND hypothesis and `⊑FD-refl` is not used.  `∥⁺`'s recursion
-- re-heads on the list's head, exactly as `⨅⁺`'s does.
--
-- NO SIDE CONDITION, for the same reason Layer 8 needs none: `∥-mono-⊑FD` is
-- unconditional (no `Sep`, no `Disj`, no `OffersOnly`, no divergence-freedom), so nothing
-- accumulates along the fold.
-------------------------------------------------------------------------------------

-- `∥⁺` is ⊑FD-monotone in its head and (pointwise) in its tail list, for any shared
-- synchronisation set, unconditionally
∥⁺-mono-⊑FD : ∀ {ℓr} (A : EventSet) {P₁ P₂ : PTree E (ExtI E) (⊤ {ℓr})}
                {Ps Qs : List (PTree E (ExtI E) (⊤ {ℓr}))}
            → P₁ ⊑FD P₂ → Pointwise _⊑FD_ Ps Qs → ∥⁺ A P₁ Ps ⊑FD ∥⁺ A P₂ Qs
∥⁺-mono-⊑FD A hP []ᵖ       = hP
∥⁺-mono-⊑FD A hP (q ∷ᵖ qs) = ∥-mono-⊑FD A hP (∥⁺-mono-⊑FD A q qs)

-- `∥Fin` is ⊑FD-monotone in its `Fin (suc n)`-indexed family, pointwise and
-- unconditionally
∥Fin-mono-⊑FD : ∀ {ℓr} (A : EventSet) {n : ℕ} {f g : Fin (suc n) → PTree E (ExtI E) (⊤ {ℓr})}
              → (∀ i → f i ⊑FD g i) → ∥Fin A n f ⊑FD ∥Fin A n g
∥Fin-mono-⊑FD A {n = zero}  h = h fzero
∥Fin-mono-⊑FD A {n = suc n} h =
  ∥-mono-⊑FD A (h fzero) (∥Fin-mono-⊑FD A (λ i → h (fsuc i)))

-------------------------------------------------------------------------------------
-- Layer 10 : the STABLE-FAILURES (`⊑F`) ANALOGUES, UNCONDITIONALLY.
--
-- `Par-mono-⊑F` and its folds are the `_⊑F_` cousins of Layers 7-9.  They are
-- UNCONDITIONAL — no divergence-freedom, no `Sep`/`Disj`/`OffersOnly`, nothing beyond a
-- pointwise `⊑F` hypothesis on each operand — and they need NO DIVERGENCE LAYER AT ALL.
--
-- Why the divergence machinery disappears.  `_⊑F_` (`Semantics.Failures`:42) is
--     P ⊑F Q  =  ∀ s X → failures Q s X → failures P s X ,
-- a plain failures-to-failures map: neither its hypothesis nor its conclusion has a
-- `divergences` disjunct, unlike `_⊑F⊥_` whose conclusion is
-- `failures P s X ⊎ divergences P s`.  Consequently:
--   • `op-transfer-stable`/`op-transfer-ret` (Layer 4) already fed only `inj₁`
--     (failures) arguments INTO their `⊑F⊥` hypotheses; it was purely their `⊎`-valued
--     RESULT that forced `Par-mono-fail` to branch 4 ways per normal form.  Their `⊑F`
--     versions below return a bare failure (resp. a bare terminated run), so each of the
--     three `ParNormal` cases collapses to its single `Par-failures-intro` recombination.
--   • Nothing ever produces a composite divergence, so Layer 5 in its entirety
--     (`Par-div-out-L/R/2`, `ParInter-truncL/R/2`, `div-extension-closed`,
--     `Par-div-intro`, `FD→trace⊥`) is dead weight here, and there is NO `Par-mono-⊑D`
--     counterpart to prove or to pair up with: `Par-mono-⊑F` IS the headline.
-- The failures decomposition/classification core is reused VERBATIM: Layer 2's
-- `Par-stable-normal`, Layer 3's `routeL`/`routeR` ban-set carving with
-- `routeL-covers`/`routeR-covers`/`route-rebuild`/`ret-routeL-cover`/`ret-routeR-cover`,
-- and `Par-failures-elim`/`Par-failures-intro` — all of which are divergence-free
-- already.  Only Layer 4 and Layer 6 get `⊑F` twins (four short definitions).
--
-- Companion law: `CSP.Laws.FD.HideMonoFD`'s `Hide-mono-⊑F` (also unconditional, for the
-- same reason).  Together they let a `⊑F` refinement be composed up through an operator
-- tree and then pushed through a hide — the route that unconditional `Hide-mono-⊑FD`
-- (FALSE) and conditional `Hide-mono-⊑FD-df` (needs divergence-freedom of the refined
-- side's hide) cannot offer.
--
-- Classical strength: unchanged and NOT new — the recombination still goes through
-- `Par-stable`, hence through `ParallelRefusals`' fixed `offer-LEM` interface (certified
-- `dne`-derivable in `CSP.Laws.ClassicalFromLEM`), exactly as `Par-mono-⊑FD` does.  No
-- new postulate.
-------------------------------------------------------------------------------------

-- Layer-4 twin: transfer a stable target residual through a `⊑F` hypothesis.  Same
-- witness as `op-transfer-stable`, but `⊑F` hands back a bare failure (no `⊎ divergences`).
op-transfer-stable-F : ∀ {ℓr} {R₁ : Set ℓr}
                       {P₁ P₂ P₂* : PTree E (ExtI E) R₁} {sP : List (Event√ R₁)}
                       {BP : Event√ R₁ → Set ℓr}
                     → P₁ ⊑F P₂
                     → P₂ ⟹⟨ sP ⟩ P₂* → isStable P₂*
                     → (∀ e → BP e → MaxRef P₂* e)
                     → failures P₁ sP BP
op-transfer-stable-F {P₂* = P₂*} {sP = sP} {BP = BP} fF run st covers =
  fF sP BP (P₂* , run , (st , covers))

-- Layer-4 twin: transfer a TERMINATED target residual through a `⊑F` hypothesis, via
-- the same √-extension trick as `op-transfer-ret` (extend the run by the `√ r` tick into
-- an empty-ban failure, push it through, split the tick back off).  The `⊑F` conclusion
-- has no divergence disjunct, so `div-√-truncate` is not needed.
op-transfer-ret-F : ∀ {ℓr} {R₁ : Set ℓr}
                    {P₁ P₂ P₂* : PTree E (ExtI E) R₁} {sP : List (Event√ R₁)} {r : R₁}
                  → P₁ ⊑F P₂
                  → P₂ ⟹⟨ sP ⟩ P₂* → PTree.force P₂* ≡ ret r
                  → Σ[ P₁ᵣ ∈ PTree E (ExtI E) R₁ ]
                      ((P₁ ⟹⟨ sP ⟩ P₁ᵣ) × (PTree.force P₁ᵣ ≡ ret r))
op-transfer-ret-F {ℓr = ℓr} {sP = sP} {r = r} fF run eqret
  with fF (sP ++ √ r ∷ []) (λ _ → Lift ℓr ⊥) (term→√failure run eqret)
... | T , run√ , _ = √-run-split-gen sP run√

-- Layer-6 twin: recombine the per-operand `⊑F` transfers of a decomposed target failure.
-- One clause per `ParNormal` case, each a single `Par-failures-intro` — the 4-way
-- divergence branching of `Par-mono-fail` has no counterpart.
Par-mono-fail-F : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                  {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
                  {s : List (Event√ R)} {X : Event√ R → Set ℓr}
                  {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)}
                  {P₂* : PTree E (ExtI E) R₁} {Q₂* : PTree E (ExtI E) R₂}
                → P₁ ⊑F P₂ → Q₁ ⊑F Q₂
                → P₂ ⟹⟨ sP ⟩ P₂* → Q₂ ⟹⟨ sQ ⟩ Q₂*
                → ParInter A merge sP sQ s
                → ParNormal P₂* Q₂*
                → ParRef A X (MaxRef P₂*) (MaxRef Q₂*)
                → failures (Par A merge P₁ Q₁) s X
-- both operands stable
Par-mono-fail-F A merge {P₁ = P₁} {Q₁ = Q₁} {X = X} {P₂* = P₂*} {Q₂* = Q₂*}
    fP fQ rP rQ inter (inj₁ (stP , stQ)) pr
  with op-transfer-stable-F fP rP stP (routeL-covers A X (MaxRef P₂*) (MaxRef Q₂*) pr)
     | op-transfer-stable-F fQ rQ stQ (routeR-covers A X (MaxRef P₂*) (MaxRef Q₂*) pr)
... | P₁* , rP₁ , refP | Q₁* , rQ₁ , refQ =
      Par-failures-intro A merge P₁ Q₁ rP₁ rQ₁ inter
        (Par-stable A merge P₁* Q₁* (proj₁ refP) (proj₁ refQ))
        (route-rebuild A X (MaxRef P₂*) (MaxRef Q₂*) pr (proj₂ refP) (proj₂ refQ))
-- left operand terminated, right stable
Par-mono-fail-F A merge {P₁ = P₁} {Q₁ = Q₁} {X = X} {P₂* = P₂*} {Q₂* = Q₂*}
    fP fQ rP rQ inter (inj₂ (inj₁ (r₁ , eqP , stQ))) pr
  with op-transfer-ret-F fP rP eqP
     | op-transfer-stable-F fQ rQ stQ (routeR-covers A X (MaxRef P₂*) (MaxRef Q₂*) pr)
... | P₁ᵣ , rP₁ , feP | Q₁* , rQ₁ , refQ =
      Par-failures-intro A merge P₁ Q₁ rP₁ rQ₁ inter
        (Par-stable-termL A merge P₁ᵣ Q₁* feP (proj₁ refQ))
        (route-rebuild A X (MaxRef P₂*) (MaxRef Q₂*) pr
          (ret-routeL-cover A X (MaxRef P₂*) (MaxRef Q₂*) pr feP) (proj₂ refQ))
-- left operand stable, right terminated (mirror)
Par-mono-fail-F A merge {P₁ = P₁} {Q₁ = Q₁} {X = X} {P₂* = P₂*} {Q₂* = Q₂*}
    fP fQ rP rQ inter (inj₂ (inj₂ (stP , r₂ , eqQ))) pr
  with op-transfer-stable-F fP rP stP (routeL-covers A X (MaxRef P₂*) (MaxRef Q₂*) pr)
     | op-transfer-ret-F fQ rQ eqQ
... | P₁* , rP₁ , refP | Q₁ᵣ , rQ₁ , feQ =
      Par-failures-intro A merge P₁ Q₁ rP₁ rQ₁ inter
        (Par-stable-termR A merge P₁* Q₁ᵣ (proj₁ refP) feQ)
        (route-rebuild A X (MaxRef P₂*) (MaxRef Q₂*) pr
          (proj₂ refP) (ret-routeR-cover A X (MaxRef P₂*) (MaxRef Q₂*) pr feQ))

-- HEADLINE (stable failures): parallel composition is ⊑F-monotone in BOTH operands,
-- unconditionally.  Decompose the target failure (`Par-failures-elim`), classify the
-- stable leaf (`Par-stable-normal`), transfer + recombine (`Par-mono-fail-F`).
Par-mono-⊑F : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
              {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
            → P₁ ⊑F P₂ → Q₁ ⊑F Q₂
            → (Par A merge P₁ Q₁) ⊑F (Par A merge P₂ Q₂)
Par-mono-⊑F A merge {P₁} {P₂} {Q₁} {Q₂} hP hQ s X f
  with Par-failures-elim A merge {P = P₂} {Q = Q₂} f
... | sP , sQ , P₂* , Q₂* , rP , rQ , inter , stPar , pr =
      Par-mono-fail-F A merge hP hQ rP rQ inter
                      (Par-stable-normal A merge P₂* Q₂* stPar) pr

-- CSP interface parallel (⊤-merge) is ⊑F-monotone
∥-mono-⊑F : ∀ {ℓr} (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr})}
          → P₁ ⊑F P₂ → Q₁ ⊑F Q₂ → (P₁ ∥⇘ A ⇙ Q₁) ⊑F (P₂ ∥⇘ A ⇙ Q₂)
∥-mono-⊑F A = Par-mono-⊑F A (λ _ _ → tt)

-- interleaving is ⊑F-monotone
⦀-mono-⊑F : ∀ {ℓr} {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr})}
          → P₁ ⊑F P₂ → Q₁ ⊑F Q₂ → (P₁ ⦀ Q₁) ⊑F (P₂ ⦀ Q₂)
⦀-mono-⊑F = Par-mono-⊑F ∅ES (λ _ _ → tt)

-- `⦀Fin` is ⊑F-monotone in its `Fin`-indexed family (base `⦀Fin zero f = Skip`)
⦀Fin-mono-⊑F : ∀ {ℓr} {n : ℕ} {f g : Fin n → PTree E (ExtI E) (⊤ {ℓr})}
             → (∀ i → f i ⊑F g i) → ⦀Fin n f ⊑F ⦀Fin n g
⦀Fin-mono-⊑F {n = zero}  h = ⊑F-refl Skip
⦀Fin-mono-⊑F {n = suc n} h = ⦀-mono-⊑F (h fzero) (⦀Fin-mono-⊑F (λ i → h (fsuc i)))

-- `⦀⋆` is ⊑F-monotone in its list of operands (base `⦀⋆ [] = Skip`)
⦀⋆-mono-⊑F : ∀ {ℓr} {Ps Qs : List (PTree E (ExtI E) (⊤ {ℓr}))}
           → Pointwise _⊑F_ Ps Qs → ⦀⋆ Ps ⊑F ⦀⋆ Qs
⦀⋆-mono-⊑F []ᵖ       = ⊑F-refl Skip
⦀⋆-mono-⊑F (p ∷ᵖ ps) = ⦀-mono-⊑F p (⦀⋆-mono-⊑F ps)

-- `∥⁺` is ⊑F-monotone in head + tail list (non-empty fold: `∥⁺ A P [] = P`)
∥⁺-mono-⊑F : ∀ {ℓr} (A : EventSet) {P₁ P₂ : PTree E (ExtI E) (⊤ {ℓr})}
               {Ps Qs : List (PTree E (ExtI E) (⊤ {ℓr}))}
           → P₁ ⊑F P₂ → Pointwise _⊑F_ Ps Qs → ∥⁺ A P₁ Ps ⊑F ∥⁺ A P₂ Qs
∥⁺-mono-⊑F A hP []ᵖ       = hP
∥⁺-mono-⊑F A hP (q ∷ᵖ qs) = ∥-mono-⊑F A hP (∥⁺-mono-⊑F A q qs)

-- `∥Fin` is ⊑F-monotone in its `Fin (suc n)`-indexed family (non-empty fold)
∥Fin-mono-⊑F : ∀ {ℓr} (A : EventSet) {n : ℕ} {f g : Fin (suc n) → PTree E (ExtI E) (⊤ {ℓr})}
             → (∀ i → f i ⊑F g i) → ∥Fin A n f ⊑F ∥Fin A n g
∥Fin-mono-⊑F A {n = zero}  h = h fzero
∥Fin-mono-⊑F A {n = suc n} h =
  ∥-mono-⊑F A (h fzero) (∥Fin-mono-⊑F A (λ i → h (fsuc i)))
