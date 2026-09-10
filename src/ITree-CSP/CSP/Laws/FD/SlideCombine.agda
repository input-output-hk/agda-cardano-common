{-# OPTIONS --guardedness #-}

-- Failures-divergences law (U13.21, ▷-combine), MENU form, built FD-direct, no DecEq R:
--
--   slide-combine-FD :
--     (((pchoice vP) ▷ (pchoice vQ)) ▷ T)  ≈FD  ((pchoice (mergeVis vP vQ)) ▷ T)
--
-- Roscoe's combine law  (?x:A → P) ▷ (?x:B → Q) ▷ R … : in this spike the combine
-- continuation `(P⊓Q)◁x∈A∩B▷(P◁x∈A▷Q)` over A∪B is EXACTLY `mergeVis vP vQ` (the same
-- merge as □-step: both-offer → just (p⊓q), A-only → just p, B-only → just q,
-- neither → nothing).  The OUTER `▷ T` is essential: without it the two sides differ
-- in their ⟨⟩-refusals; with it both are unstable (each reaches T via a timeout) with
-- the SAME ⟨⟩-refusals, and the law holds FD-direct.
--
-- The proof recurses MANUALLY on the slides' big-steps (no ▷-failures-elim ⇒ no DecEq),
-- exactly the DecEq-free pattern of CSP.Laws.FD.SlideNoHist, generalised to a nested
-- slide on the left and the merged menu on the right.  It needs a general
-- pchoice-v failures/divergence decomposition (`pchoice-⟹-inv` and friends), built
-- here for arbitrary `v` (the existing menu/pfx lemmas only handle special shapes).

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤) renaming (tt to tt0)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.SlideCombine {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Refuses)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; div-extension-closed; failures⊥;
         _⊇F⊥_; _⊇D_; _⊑FD_; _≈FD_)
open import CSP.Laws.Traces.TraceLaws E-≟ using (▷-ev-L; ▷-τ-L)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (NonRet; mergeVis-L-eq; mergeVis-R-eq; mergeVis-LQ-eq)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (▷-timeout; ▷-τ-elim; ▷-ev-elim)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (▷-reach-div; div-τ-prepend; div-ev-prepend; fail-τ-prepend; fail-ev-prepend;
         ▷-unstable; stable-no-τ)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-failures←l; ⊓-failures←r; ⊓-div→; ⊓-div←l; ⊓-div←r;
         ⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r)

private
  variable
    ℓr ℓx : Level

-------------------------------------------------------------------------------------
-- General `pchoice v` facts.  force (pchoice v) = react v ∅t : stable, visible-only,
-- τ-free.  Its big-steps either stop (W = pchoice v, s = []) or peel one offered
-- event (cont = the M with v at a ≡ just M).
-------------------------------------------------------------------------------------

module _ {ℓr} {R : Set ℓr} where

  -- the canonical pchoice event step (mirror of menu-ev / pfx-ev-step)
  pchoice-ev : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
               {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
             → v at a ≡ just M
             → (pchoice v) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► M
  pchoice-ev v {at} {a} br = sVis {at = at} {a = a} refl br

  pchoice-stable : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                 → isStable (pchoice v)
  pchoice-stable v _ _ = refl

  -- invert a single visible step out of pchoice v : recover the offered event.
  pchoice-ev-inv : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                   {e : Event√ R} {W : PTree E (ExtI E) R}
                 → (pchoice v) ─[ ev e ]─► W
                 → Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ]
                     (e ≡ evl (evLabel (proj₁ at) (proj₂ at) a) × v at a ≡ just W)
  pchoice-ev-inv v (sRet ())
  pchoice-ev-inv v (sVis {at = at} {a = a} refl br) = at , a , refl , br

  -- every big-step out of a pchoice v is empty or peels one offered event.
  pchoice-⟹-inv : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                   {s : List (Event√ R)} {W : PTree E (ExtI E) R}
                 → (pchoice v) ⟹⟨ s ⟩ W
                 → (W ≡ pchoice v × s ≡ [])
                 ⊎ (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] Σ[ M ∈ PTree E (ExtI E) R ]
                      Σ[ t ∈ List (Event√ R) ]
                      (v at a ≡ just M × s ≡ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ t
                       × M ⟹⟨ t ⟩ W))
  pchoice-⟹-inv v ⟹-refl              = inj₁ (refl , refl)
  pchoice-⟹-inv v (⟹-τ (sSil ()) _)
  pchoice-⟹-inv v (⟹-τ (sTau refl ()) _)
  pchoice-⟹-inv v (⟹-ev (sRet ()) _)
  pchoice-⟹-inv v (⟹-ev (sVis {at = at} {a = a} refl br) rest) =
    inj₂ (at , a , _ , _ , br , refl , rest)

  -- a refusal of pchoice v carries its stability (used only to discharge bases).
  -- failures of pchoice v.
  pchoice-failures→ : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                      {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                    → failures (pchoice v) s X
                    → ((s ≡ []) × Refuses (pchoice v) X)
                    ⊎ (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] Σ[ M ∈ PTree E (ExtI E) R ]
                         Σ[ t ∈ List (Event√ R) ]
                         (v at a ≡ just M × s ≡ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ t
                          × failures M t X))
  pchoice-failures→ v (W , pw , ref) with pchoice-⟹-inv v pw
  ... | inj₁ (refl , refl)                       = inj₁ (refl , ref)
  ... | inj₂ (at , a , M , t , br , refl , reach) = inj₂ (at , a , M , t , br , refl , (W , reach , ref))

  -- divergences of pchoice v : peel one offered event (the node is stable, so the
  -- empty big-step is non-divergent).
  pchoice-div→ : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                 {s : List (Event√ R)}
               → divergences (pchoice v) s
               → Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] Σ[ M ∈ PTree E (ExtI E) R ]
                   Σ[ t ∈ List (Event√ R) ]
                   (v at a ≡ just M × s ≡ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ t × divergences M t)
  pchoice-div→ v d with pchoice-⟹-inv v (d .IsDivergence.reach)
  ... | inj₁ (eqW , _) =
          ⊥-elim (stable-no-τ (pchoice-stable v)
                    (subst Diverges eqW (d .IsDivergence.divwit) .Diverges.step))
  ... | inj₂ (at , a , M , t , br , eqPrefix , reach) =
          at , a , M , t ++ d .IsDivergence.suffix , br
            , trans (d .IsDivergence.split) (cong (_++ d .IsDivergence.suffix) eqPrefix)
            , record { prefix  = t                  ; suffix = d .IsDivergence.suffix
                     ; split   = refl               ; witness = d .IsDivergence.witness
                     ; reach   = reach              ; divwit = d .IsDivergence.divwit }

-------------------------------------------------------------------------------------
-- Merge inversion: a merged offer  mergeVis vP vQ at a ≡ just M  is exactly one of
-- the three cases (A-only / B-only / overlap), recovering the operand continuations.
-------------------------------------------------------------------------------------

  merge-just-inv : (vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                   {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
                 → mergeVis vP vQ at a ≡ just M
                 → (Σ[ P₁ ∈ PTree E (ExtI E) R ] (vP at a ≡ just P₁ × vQ at a ≡ nothing × M ≡ P₁))
                 ⊎ (Σ[ Q₁ ∈ PTree E (ExtI E) R ] (vP at a ≡ nothing × vQ at a ≡ just Q₁ × M ≡ Q₁))
                 ⊎ (Σ[ P₁ ∈ PTree E (ExtI E) R ] Σ[ Q₁ ∈ PTree E (ExtI E) R ]
                      (vP at a ≡ just P₁ × vQ at a ≡ just Q₁ × M ≡ P₁ ⊓ Q₁))
  merge-just-inv vP vQ {at} {a} br with vP at a | vQ at a
  ... | just P₁ | nothing = inj₁ (P₁ , refl , refl , sym (just-injective br))
  ... | nothing | just Q₁ = inj₂ (inj₁ (Q₁ , refl , refl , sym (just-injective br)))
  ... | just P₁ | just Q₁ = inj₂ (inj₂ (P₁ , Q₁ , refl , refl , sym (just-injective br)))
  ... | nothing | nothing = case br of λ ()

-------------------------------------------------------------------------------------
-- THE LAW.  Fix  vP vQ T.  Write
--   S   = (pchoice vP) ▷ (pchoice vQ)            -- force S = react vP (▷-slide …)
--   LHS = S ▷ T                                  -- unstable (outer + inner timeouts)
--   RHS = (pchoice (mergeVis vP vQ)) ▷ T         -- unstable (single timeout)
-------------------------------------------------------------------------------------

module _ {ℓr} {R : Set ℓr}
         (vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         (T : PTree E (ExtI E) R) where

  private
    PC PQc M : PTree E (ExtI E) R
    PC  = pchoice vP
    PQc = pchoice vQ
    M   = pchoice (mergeVis vP vQ)

    S : PTree E (ExtI E) R
    S = PC ▷ PQc

    LHS RHS : PTree E (ExtI E) R
    LHS = S ▷ T
    RHS = M ▷ T

    mv : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
    mv = mergeVis vP vQ

  -- the LHS direct event step  (S ▷ T) ─[ev a]→ P₁  when  vP at a ≡ just P₁
  LHS-evP : {at : AnyTypes E} {a : proj₁ at} {P₁ : PTree E (ExtI E) R}
          → vP at a ≡ just P₁
          → LHS ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P₁
  LHS-evP brP = ▷-ev-L (▷-ev-L (pchoice-ev vP brP))

  -- the LHS inner-timeout-slid τ-step  (S ▷ T) ─[τ]→ (PQc ▷ T)
  LHS-innerτ : LHS ─[ τ ]─► (PQc ▷ T)
  LHS-innerτ = ▷-τ-L (▷-timeout PC PQc refl tt0)

  -- the LHS event-via-inner-timeout reaches Q₁ from (PQc ▷ T) when vQ at a ≡ just Q₁
  PQcT-evQ : {at : AnyTypes E} {a : proj₁ at} {Q₁ : PTree E (ExtI E) R}
           → vQ at a ≡ just Q₁
           → (PQc ▷ T) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► Q₁
  PQcT-evQ brQ = ▷-ev-L (pchoice-ev vQ brQ)

  -- the LHS outer-timeout τ-step  (S ▷ T) ─[τ]→ T
  LHS-outerτ : LHS ─[ τ ]─► T
  LHS-outerτ = ▷-timeout S T refl tt0

  -- the RHS outer-timeout τ-step  (M ▷ T) ─[τ]→ T
  RHS-outerτ : RHS ─[ τ ]─► T
  RHS-outerτ = ▷-timeout M T refl tt0

  -- the RHS merged event step  (M ▷ T) ─[ev a]→ Mc  when  mv at a ≡ just Mc
  RHS-evM : {at : AnyTypes E} {a : proj₁ at} {Mc : PTree E (ExtI E) R}
          → mv at a ≡ just Mc
          → RHS ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► Mc
  RHS-evM brM = ▷-ev-L (pchoice-ev mv brM)

  -----------------------------------------------------------------------------------
  -- DIVERGENCES.
  -----------------------------------------------------------------------------------

  -- `▷-reach-div` projects a divergence onto an operand AT THE BIG-STEP PREFIX
  -- `d .prefix`; `div-extension-closed` re-extends it to `d.prefix ++ d.suffix`, and the
  -- final `subst (... ) (sym (d.split))` lands it back on `s`, exactly as SlideNoHist's
  -- S→RHS-D.  The worker `*-at` produces the result at `prefix ++ suffix`.

  -- RHS → LHS : divergences RHS s → divergences LHS s        (LHS ⊇D RHS)
  RHS→LHS-D-at : ∀ {s} (d : divergences RHS s)
               → divergences LHS (d .IsDivergence.prefix ++ d .IsDivergence.suffix)
  RHS→LHS-D-at d with ▷-reach-div M T (d .IsDivergence.reach) (d .IsDivergence.divwit)
  ... | inj₂ dT  = div-τ-prepend LHS-outerτ (div-extension-closed dT)
  ... | inj₁ dM with pchoice-div→ mv (div-extension-closed {t = d .IsDivergence.suffix} dM)
  ...   | (at , a , Mc , t , brM , eqs , dMc) =
            subst (divergences LHS) (sym eqs) (body (merge-just-inv vP vQ brM))
    where
      body : _ → divergences LHS (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ t)
      body (inj₁ (P₁ , brP , brQ , refl)) = div-ev-prepend (LHS-evP brP) dMc
      body (inj₂ (inj₁ (Q₁ , brP , brQ , refl))) =
        div-τ-prepend LHS-innerτ (div-ev-prepend (PQcT-evQ brQ) dMc)
      body (inj₂ (inj₂ (P₁ , Q₁ , brP , brQ , refl))) with ⊓-div→ P₁ Q₁ dMc
      ... | inj₁ dP₁ = div-ev-prepend (LHS-evP brP) dP₁
      ... | inj₂ dQ₁ = div-τ-prepend LHS-innerτ (div-ev-prepend (PQcT-evQ brQ) dQ₁)

  RHS→LHS-D : ∀ {s} → divergences RHS s → divergences LHS s
  RHS→LHS-D d = subst (divergences LHS) (sym (d .IsDivergence.split)) (RHS→LHS-D-at d)

  -- inner step: a divergence of S = PC ▷ PQc at trace p maps to RHS at the SAME p.
  -- Project onto PC / PQc (▷-reach-div drops the inner suffix), re-extend by that
  -- suffix, peel the offered event and map via the merge.
  S-div→RHS-at : ∀ {p} (dS : divergences S p)
               → divergences RHS (dS .IsDivergence.prefix ++ dS .IsDivergence.suffix)
  S-div→RHS-at dS with ▷-reach-div PC PQc (dS .IsDivergence.reach) (dS .IsDivergence.divwit)
  ... | inj₁ dPC with pchoice-div→ vP (div-extension-closed {t = dS .IsDivergence.suffix} dPC)
  ...   | (at , a , P₁ , t , brP , eqs , dP₁) =
            subst (divergences RHS) (sym eqs) (bodyP (vQ at a) refl)
    where
      bodyP : (m : _) → vQ at a ≡ m → divergences RHS (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ t)
      bodyP nothing   eqQ = div-ev-prepend (RHS-evM (mergeVis-L-eq {vP = vP} {vQ = vQ} brP eqQ)) dP₁
      bodyP (just Q₁) eqQ = div-ev-prepend (RHS-evM (mergeVis-LQ-eq {vP = vP} {vQ = vQ} brP eqQ))
                              (⊓-div←l P₁ Q₁ dP₁)
  S-div→RHS-at dS | inj₂ dPQc with pchoice-div→ vQ (div-extension-closed {t = dS .IsDivergence.suffix} dPQc)
  ...   | (at , a , Q₁ , t , brQ , eqs , dQ₁) =
            subst (divergences RHS) (sym eqs) (bodyQ (vP at a) refl)
    where
      bodyQ : (m : _) → vP at a ≡ m → divergences RHS (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ t)
      bodyQ nothing   eqP = div-ev-prepend (RHS-evM (mergeVis-R-eq {vP = vP} {vQ = vQ} eqP brQ)) dQ₁
      bodyQ (just P₁) eqP = div-ev-prepend (RHS-evM (mergeVis-LQ-eq {vP = vP} {vQ = vQ} eqP brQ))
                              (⊓-div←r P₁ Q₁ dQ₁)

  S-div→RHS : ∀ {p} → divergences S p → divergences RHS p
  S-div→RHS dS = subst (divergences RHS) (sym (dS .IsDivergence.split)) (S-div→RHS-at dS)

  -- LHS → RHS : divergences LHS s → divergences RHS s        (RHS ⊇D LHS)
  LHS→RHS-D-at : ∀ {s} (d : divergences LHS s)
               → divergences RHS (d .IsDivergence.prefix ++ d .IsDivergence.suffix)
  LHS→RHS-D-at d with ▷-reach-div S T (d .IsDivergence.reach) (d .IsDivergence.divwit)
  ... | inj₂ dT  = div-τ-prepend RHS-outerτ (div-extension-closed dT)
  ... | inj₁ dS  = div-extension-closed (S-div→RHS dS)

  LHS→RHS-D : ∀ {s} → divergences LHS s → divergences RHS s
  LHS→RHS-D d = subst (divergences RHS) (sym (d .IsDivergence.split)) (LHS→RHS-D-at d)

  -----------------------------------------------------------------------------------
  -- FAILURES (⊥).  The merge-casing crux.  Refusals pass through verbatim (every
  -- final stable W is T / P₁ / Q₁ / P₁⊓Q₁ — never a pchoice node, since each slide is
  -- unstable via its timeout), so no domain matching of refusals is needed.
  -----------------------------------------------------------------------------------

  -- prepend an A-event (direct, via vP at a ≡ just P₁) to a failures⊥ of P₁
  prependA : {at : AnyTypes E} {a : proj₁ at} {P₁ : PTree E (ExtI E) R}
             {s′ : List (Event√ R)} {B : Event√ R → Set ℓr}
           → vP at a ≡ just P₁ → failures⊥ P₁ s′ B
           → failures⊥ LHS (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s′) B
  prependA brP (inj₁ f) = inj₁ (fail-ev-prepend (LHS-evP brP) f)
  prependA brP (inj₂ d) = inj₂ (div-ev-prepend (LHS-evP brP) d)

  -- prepend a B-event (via the inner timeout, then vQ at a ≡ just Q₁) to a failures⊥ of Q₁
  prependB : {at : AnyTypes E} {a : proj₁ at} {Q₁ : PTree E (ExtI E) R}
             {s′ : List (Event√ R)} {B : Event√ R → Set ℓr}
           → vQ at a ≡ just Q₁ → failures⊥ Q₁ s′ B
           → failures⊥ LHS (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s′) B
  prependB brQ (inj₁ f) = inj₁ (fail-τ-prepend LHS-innerτ (fail-ev-prepend (PQcT-evQ brQ) f))
  prependB brQ (inj₂ d) = inj₂ (div-τ-prepend LHS-innerτ (div-ev-prepend (PQcT-evQ brQ) d))

  -- route a merged-event failure⊥ of Mc (= mv at a) to LHS
  route-RHS-ev : {at : AnyTypes E} {a : proj₁ at} {Mc : PTree E (ExtI E) R}
                 {s′ : List (Event√ R)} {B : Event√ R → Set ℓr}
               → mv at a ≡ just Mc → failures⊥ Mc s′ B
               → failures⊥ LHS (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s′) B
  route-RHS-ev brM fb with merge-just-inv vP vQ brM
  ... | inj₁ (P₁ , brP , brQ , refl)             = prependA brP fb
  ... | inj₂ (inj₁ (Q₁ , brP , brQ , refl))      = prependB brQ fb
  ... | inj₂ (inj₂ (P₁ , Q₁ , brP , brQ , refl)) with ⊓-failures⊥→ P₁ Q₁ fb
  ...   | inj₁ fP₁ = prependA brP fP₁
  ...   | inj₂ fQ₁ = prependB brQ fQ₁

  -- RHS → LHS, failures component (recursion on RHS = M ▷ T big-step)
  RHS-fail-route : ∀ {s W} {B : Event√ R → Set ℓr}
                 → RHS ⟹⟨ s ⟩ W → Refuses W B → failures⊥ LHS s B
  RHS-fail-route ⟹-refl ref = ⊥-elim (▷-unstable M T (proj₁ ref))
  RHS-fail-route (⟹-τ step rest) ref with ▷-τ-elim M T step
  ... | inj₁ refl                = inj₁ (fail-τ-prepend LHS-outerτ (_ , rest , ref))
  ... | inj₂ (M' , Mτ , refl)    = ⊥-elim (stable-no-τ (pchoice-stable mv) Mτ)
  RHS-fail-route (⟹-ev step rest) ref with pchoice-ev-inv mv (▷-ev-elim M T step)
  ... | (at , a , refl , brM)    = route-RHS-ev brM (inj₁ (_ , rest , ref))

  -- LHS ⊇F⊥ RHS
  RHS→LHS-F⊥ : ∀ {s} {B : Event√ R → Set ℓr} → failures⊥ RHS s B → failures⊥ LHS s B
  RHS→LHS-F⊥ (inj₁ (W , reach , ref)) = RHS-fail-route reach ref
  RHS→LHS-F⊥ (inj₂ d)                 = inj₂ (RHS→LHS-D d)

  -----------------------------------------------------------------------------------
  -- LHS → RHS, failures.  Symmetric crux: an LHS vP-event maps to an RHS event whose
  -- continuation is P₁ (A-only) or P₁⊓Q₁ (overlap, lift LEFT); an LHS inner-timeout
  -- vQ-event maps to an RHS event with continuation Q₁ (B-only) or P₁⊓Q₁ (overlap,
  -- lift RIGHT).
  -----------------------------------------------------------------------------------

  -- generic RHS visible-event prepend on failures⊥
  RHS-ev⊥ : {at : AnyTypes E} {a : proj₁ at} {Mc : PTree E (ExtI E) R}
            {s′ : List (Event√ R)} {B : Event√ R → Set ℓr}
          → RHS ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► Mc → failures⊥ Mc s′ B
          → failures⊥ RHS (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s′) B
  RHS-ev⊥ evs (inj₁ f) = inj₁ (fail-ev-prepend evs f)
  RHS-ev⊥ evs (inj₂ d) = inj₂ (div-ev-prepend evs d)

  -- an LHS vP-event (vP at a ≡ just P₁) → RHS event (P₁ alone, or P₁⊓Q₁ split LEFT)
  routeP : {at : AnyTypes E} {a : proj₁ at} {P₁ : PTree E (ExtI E) R}
           {s′ : List (Event√ R)} {B : Event√ R → Set ℓr}
         → vP at a ≡ just P₁ → failures⊥ P₁ s′ B
         → failures⊥ RHS (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s′) B
  routeP {at} {a} brP fb = go (vQ at a) refl
    where
      go : (m : _) → vQ at a ≡ m → failures⊥ RHS _ _
      go nothing   eqQ = RHS-ev⊥ (RHS-evM (mergeVis-L-eq {vP = vP} {vQ = vQ} brP eqQ)) fb
      go (just Q₁) eqQ = RHS-ev⊥ (RHS-evM (mergeVis-LQ-eq {vP = vP} {vQ = vQ} brP eqQ))
                           (⊓-failures⊥←l _ _ fb)

  -- an LHS vQ-event (vQ at a ≡ just Q₁) → RHS event (Q₁ alone, or P₁⊓Q₁ split RIGHT)
  routeQ : {at : AnyTypes E} {a : proj₁ at} {Q₁ : PTree E (ExtI E) R}
           {s′ : List (Event√ R)} {B : Event√ R → Set ℓr}
         → vQ at a ≡ just Q₁ → failures⊥ Q₁ s′ B
         → failures⊥ RHS (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s′) B
  routeQ {at} {a} brQ fb = go (vP at a) refl
    where
      go : (m : _) → vP at a ≡ m → failures⊥ RHS _ _
      go nothing   eqP = RHS-ev⊥ (RHS-evM (mergeVis-R-eq {vP = vP} {vQ = vQ} eqP brQ)) fb
      go (just P₁) eqP = RHS-ev⊥ (RHS-evM (mergeVis-LQ-eq {vP = vP} {vQ = vQ} eqP brQ))
                           (⊓-failures⊥←r _ _ fb)

  -- failure of (PQc ▷ T) (the inner-timeout target slid) routed to RHS
  PQcT-fail-route : ∀ {s W} {B : Event√ R → Set ℓr}
                  → (PQc ▷ T) ⟹⟨ s ⟩ W → Refuses W B → failures⊥ RHS s B
  PQcT-fail-route ⟹-refl ref = ⊥-elim (▷-unstable PQc T (proj₁ ref))
  PQcT-fail-route (⟹-τ step rest) ref with ▷-τ-elim PQc T step
  ... | inj₁ refl                = inj₁ (fail-τ-prepend RHS-outerτ (_ , rest , ref))
  ... | inj₂ (PQc' , PQcτ , refl) = ⊥-elim (stable-no-τ (pchoice-stable vQ) PQcτ)
  PQcT-fail-route (⟹-ev step rest) ref with pchoice-ev-inv vQ (▷-ev-elim PQc T step)
  ... | (at , a , refl , brQ)    = routeQ brQ (inj₁ (_ , rest , ref))

  -- LHS → RHS, failures component (recursion on LHS = S ▷ T big-step)
  LHS-fail-route : ∀ {s W} {B : Event√ R → Set ℓr}
                 → LHS ⟹⟨ s ⟩ W → Refuses W B → failures⊥ RHS s B
  LHS-fail-route ⟹-refl ref = ⊥-elim (▷-unstable S T (proj₁ ref))
  LHS-fail-route (⟹-τ step rest) ref with ▷-τ-elim S T step
  ... | inj₁ refl             = inj₁ (fail-τ-prepend RHS-outerτ (_ , rest , ref))
  ... | inj₂ (S' , Sτ , refl) with ▷-τ-elim PC PQc Sτ
  ...   | inj₁ refl              = PQcT-fail-route rest ref
  ...   | inj₂ (PC' , PCτ , refl) = ⊥-elim (stable-no-τ (pchoice-stable vP) PCτ)
  LHS-fail-route (⟹-ev step rest) ref
    with pchoice-ev-inv vP (▷-ev-elim PC PQc (▷-ev-elim S T step))
  ... | (at , a , refl , brP) = routeP brP (inj₁ (_ , rest , ref))

  -- RHS ⊇F⊥ LHS
  LHS→RHS-F⊥ : ∀ {s} {B : Event√ R → Set ℓr} → failures⊥ LHS s B → failures⊥ RHS s B
  LHS→RHS-F⊥ (inj₁ (W , reach , ref)) = LHS-fail-route reach ref
  LHS→RHS-F⊥ (inj₂ d)                 = inj₂ (LHS→RHS-D d)

-------------------------------------------------------------------------------------
-- THE LAW (U13.21, ▷-combine, MENU form): pair the two ⊇F⊥ and two ⊇D refinements.
-------------------------------------------------------------------------------------

slide-combine-FD : ∀ {ℓr} {R : Set ℓr}
                   (vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                   (T : PTree E (ExtI E) R)
                 → (((pchoice vP) ▷ (pchoice vQ)) ▷ T) ≈FD ((pchoice (mergeVis vP vQ)) ▷ T)
slide-combine-FD vP vQ T =
  (RHS→LHS-F⊥ vP vQ T , RHS→LHS-D vP vQ T) ,
  (LHS→RHS-F⊥ vP vQ T , LHS→RHS-D vP vQ T)
