{-# OPTIONS --guardedness #-}

-- Failures-divergences theory of external choice □, built FD-direct.  Uses the
-- external-choice step-inversions from TraceLawsExtChoiceMono and the (certified)
-- divergence-projection postulates □-Diverges→ / ▷-Diverges→ from ExtChoiceDivergence.
--
-- Culminates in  □-⊓-dist-FD : P □ (Q ⊓ S) ≈FD (P □ Q) ⊓ (P □ S)  — external choice
-- distributes over internal choice (FD), for FULLY GENERAL P (incl. terminating).
-- Layers: divergence elim/intro; the general □ failures elim (□-failures-elim); the
-- √-slide bridges (slide-term-fail, □→▷-term, □→▷-Pret); the distribution-specific
-- elim (□-⊓-fail-elim) and intro (□-⊓-fail-intro-L/R); the assembly (□-⊓-dist-⊒/⊑/FD).

open import Level using (Level; Lift; lift; lower)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.FD.ExtChoiceFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges; deadlock-converges)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; div-extension-closed; empty-div; failures⊥;
         _⊇F⊥_; _⊇D_; _⊑FD_; _≈FD_)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses; Offers)
-- generic stability facts, kept qualified: the local names below re-expose them in
-- the historic argument order.
import Semantics.Stability {E = E} {I = ExtI E} as S
open import CSP.Laws.FD.ExtChoiceDivergence E-≟ using (□-Diverges→; ▷-Diverges→)
open import CSP.Laws.FD.FDLawsIChoiceAssoc  E-≟
  using (⊓-div→; ⊓-failures→; ⊓-div←l; ⊓-div←r; ⊓-failures⊥←l; ⊓-failures⊥←r; ⊓-failures⊥→)
open import CSP.Laws.Bisim.Laws             E-≟ using (⊓-stepL; ⊓-stepR; ⊓-τ-inv)
open import CSP.Laws.Traces.TraceLaws       E-≟
  using (▷-τ-L; ▷-ev-L; force-▷-ret; force-▷-sil; force-▷-react)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (NonRet; □-τ-tochoice; □-τ-toslide; □-τ-tochoice-R; □-τ-toslide-R; □-ev-L;
         fL-A; fL-B; fL-C; fL-D; fL-E; fL-F; fL-G; □-mt-tag0-eq;
         mergeVis-L-eq; mergeVis-R-eq; mergeVis-LQ-eq)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (□τR; cP; cQ; sPQ; sQP; chP; chQ; □-τ-elim; viewT-τ; □-slide-PR-elim; □-slide-RQ-elim;
         □-mt-elim; ▷-timeout;
         □evR; evP; evQ; evPQ; □-ev-elim; ▷-τ-elim; ▷-ev-elim; mergeVis-elim; ret-no-τ)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- Divergence-record plumbing: build / prepend.
-------------------------------------------------------------------------------------

mk-div : {P W : PTree E (ExtI E) R} {pre : List (Event√ R)}
       → P ⟹⟨ pre ⟩ W → Diverges W → divergences P pre
mk-div {pre = pre} reach divw = record
  { prefix = pre ; suffix = [] ; split = sym (++-identityʳ pre)
  ; witness = _ ; reach = reach ; divwit = divw }

div-τ-prepend : {P P′ : PTree E (ExtI E) R} {s : List (Event√ R)}
              → P ─[ τ ]─► P′ → divergences P′ s → divergences P s
div-τ-prepend step d = record
  { prefix = d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split  = d .IsDivergence.split  ; witness = d .IsDivergence.witness
  ; reach  = ⟹-τ step (d .IsDivergence.reach) ; divwit = d .IsDivergence.divwit }

div-ev-prepend : {P P′ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)}
               → P ─[ ev e ]─► P′ → divergences P′ s → divergences P (e ∷ s)
div-ev-prepend {e = e} step d = record
  { prefix = e ∷ d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split  = cong (e ∷_) (d .IsDivergence.split) ; witness = d .IsDivergence.witness
  ; reach  = ⟹-ev step (d .IsDivergence.reach) ; divwit = d .IsDivergence.divwit }

-------------------------------------------------------------------------------------
-- Divergence elimination: a divergence reached from P □ Q (resp. A ▷ B) projects to
-- one operand.  Structural recursion on the big-step `reach`; the base case uses the
-- (certified) □-/▷-Diverges→, the merged-event case uses the ⊓ divergence split.
-------------------------------------------------------------------------------------

□-reach-div : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
              {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
            → (P □ Q) ⟹⟨ pre ⟩ W → Diverges W → divergences P pre ⊎ divergences Q pre
▷-reach-div : (A B : PTree E (ExtI E) R)
              {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
            → (A ▷ B) ⟹⟨ pre ⟩ W → Diverges W → divergences A pre ⊎ divergences B pre

□-reach-div P Q ⟹-refl divW with □-Diverges→ divW
... | inj₁ dP = inj₁ (empty-div dP)
... | inj₂ dQ = inj₂ (empty-div dQ)
□-reach-div P Q (⟹-τ step rest) divW with □-τ-elim P Q step
... | cP refl = inj₁ (mk-div rest divW)
... | cQ refl = inj₂ (mk-div rest divW)
... | chP P' Pτ refl with □-reach-div P' Q rest divW
...   | inj₁ dP' = inj₁ (div-τ-prepend Pτ dP')
...   | inj₂ dQ  = inj₂ dQ
□-reach-div P Q (⟹-τ step rest) divW | chQ Q' Qτ refl with □-reach-div P Q' rest divW
...   | inj₁ dP  = inj₁ dP
...   | inj₂ dQ' = inj₂ (div-τ-prepend Qτ dQ')
□-reach-div P Q (⟹-τ step rest) divW | sPQ P' Pτ refl with ▷-reach-div P' Q rest divW
...   | inj₁ dP' = inj₁ (div-τ-prepend Pτ dP')
...   | inj₂ dQ  = inj₂ dQ
□-reach-div P Q (⟹-τ step rest) divW | sQP Q' Qτ refl with ▷-reach-div Q' P rest divW
...   | inj₁ dQ' = inj₂ (div-τ-prepend Qτ dQ')
...   | inj₂ dP  = inj₁ dP
□-reach-div P Q (⟹-ev step rest) divW with □-ev-elim P Q step
... | evP Pev = inj₁ (div-ev-prepend Pev (mk-div rest divW))
... | evQ Qev = inj₂ (div-ev-prepend Qev (mk-div rest divW))
... | evPQ {P₁ = P₁} {Q₁ = Q₁} Pev Qev with ⊓-div→ P₁ Q₁ (mk-div rest divW)
...   | inj₁ dP₁ = inj₁ (div-ev-prepend Pev dP₁)
...   | inj₂ dQ₁ = inj₂ (div-ev-prepend Qev dQ₁)

▷-reach-div A B ⟹-refl divW with ▷-Diverges→ divW
... | inj₁ dA = inj₁ (empty-div dA)
... | inj₂ dB = inj₂ (empty-div dB)
▷-reach-div A B (⟹-τ step rest) divW with ▷-τ-elim A B step
... | inj₁ refl            = inj₂ (mk-div rest divW)
... | inj₂ (A' , Aτ , refl) with ▷-reach-div A' B rest divW
...   | inj₁ dA' = inj₁ (div-τ-prepend Aτ dA')
...   | inj₂ dB  = inj₂ dB
▷-reach-div A B (⟹-ev step rest) divW =
  inj₁ (div-ev-prepend (▷-ev-elim A B step) (mk-div rest divW))

-- divergences (P □ Q) ⊆ divergences P ∪ divergences Q
□-div-elim : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {s : List (Event√ R)}
           → divergences (P □ Q) s → divergences P s ⊎ divergences Q s
□-div-elim {P = P} {Q = Q} d
  with □-reach-div P Q (d .IsDivergence.reach) (d .IsDivergence.divwit)
... | inj₁ dP = inj₁ (subst (divergences P) (sym (d .IsDivergence.split))
                            (div-extension-closed dP))
... | inj₂ dQ = inj₂ (subst (divergences Q) (sym (d .IsDivergence.split))
                            (div-extension-closed dQ))

-------------------------------------------------------------------------------------
-- Divergence INTRODUCTION: a divergence of one operand lifts to P □ Q.  A diverging
-- run is an infinite τ-chain; we propagate it through the operator (□-Diverges-* /
-- ▷-Diverges-L), then lift the leading big-step (□-/▷-reach-intro-*).
-------------------------------------------------------------------------------------

-- a divergence (infinite τ-chain) of P slides through P ▷ Q on the left
▷-Diverges-L : {P Q : PTree E (ExtI E) R} → Diverges P → Diverges (P ▷ Q)
▷-Diverges-L {Q = Q} d .Diverges.next = (d .Diverges.next) ▷ Q
▷-Diverges-L d .Diverges.step = ▷-τ-L (d .Diverges.step)
▷-Diverges-L d .Diverges.rest = ▷-Diverges-L (d .Diverges.rest)

-- Q is FIXED non-terminated throughout: each P-τ fires the merged-τ branch (→ ·□ Q),
-- so the corecursion keeps the same Q/eqQ/ntQ (no `with` ⇒ guardedness is preserved).
□-Diverges-choice-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {nQ : NodeKind E (ExtI E) R}
                    → PTree.force Q ≡ nQ → NonRet nQ → Diverges P → Diverges (P □ Q)
□-Diverges-choice-L P Q eqQ ntQ d .Diverges.next = (d .Diverges.next) □ Q
□-Diverges-choice-L P Q eqQ ntQ d .Diverges.step = □-τ-tochoice P Q (d .Diverges.step) eqQ ntQ
□-Diverges-choice-L P Q eqQ ntQ d .Diverges.rest =
  □-Diverges-choice-L _ Q eqQ ntQ (d .Diverges.rest)

-- a divergence of P propagates through P □ Q: Q live ⇒ choice (·□ Q), Q terminated ⇒
-- slide to ·▷ Q, where it keeps diverging via ▷-Diverges-L.  Non-recursive: it only
-- dispatches (on force Q) to the two with-free productive helpers.
□-Diverges-L : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} → Diverges P → Diverges (P □ Q)
□-Diverges-L {P = P} {Q = Q} d with PTree.force Q in eqQ
... | ret _    = record { step = □-τ-toslide P Q (d .Diverges.step) eqQ
                        ; rest = ▷-Diverges-L (d .Diverges.rest) }
... | sil _    = □-Diverges-choice-L P Q eqQ tt d
... | react _ _ = □-Diverges-choice-L P Q eqQ tt d

-- mirror on the right
□-Diverges-choice-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {nP : NodeKind E (ExtI E) R}
                    → PTree.force P ≡ nP → NonRet nP → Diverges Q → Diverges (P □ Q)
□-Diverges-choice-R P Q eqP ntP d .Diverges.next = P □ (d .Diverges.next)
□-Diverges-choice-R P Q eqP ntP d .Diverges.step = □-τ-tochoice-R P Q (d .Diverges.step) eqP ntP
□-Diverges-choice-R P Q eqP ntP d .Diverges.rest =
  □-Diverges-choice-R P _ eqP ntP (d .Diverges.rest)

□-Diverges-R : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} → Diverges Q → Diverges (P □ Q)
□-Diverges-R {P = P} {Q = Q} d with PTree.force P in eqP
... | ret _    = record { step = □-τ-toslide-R P Q (d .Diverges.step) eqP
                        ; rest = ▷-Diverges-L (d .Diverges.rest) }
... | sil _    = □-Diverges-choice-R P Q eqP tt d
... | react _ _ = □-Diverges-choice-R P Q eqP tt d

-- deadlock cannot lead anywhere (used to discharge the √-commit case)
deadlock-⟹-[] : {W : PTree E (ExtI E) R} {s : List (Event√ R)}
              → deadlock ⟹⟨ s ⟩ W → s ≡ [] × W ≡ deadlock
deadlock-⟹-[] ⟹-refl              = refl , refl
deadlock-⟹-[] (⟹-τ (sSil ()) _)
deadlock-⟹-[] (⟹-τ (sTau refl ()) _)
deadlock-⟹-[] (⟹-ev (sRet ()) _)
deadlock-⟹-[] (⟹-ev (sVis refl ()) _)

-- lift a left visible/√ step + a continuing divergence into a divergence of P □ Q
□-ev-lift-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {P₁ W : PTree E (ExtI E) R}
              {e : Event√ R} {p′ : List (Event√ R)}
            → P ─[ ev e ]─► P₁ → P₁ ⟹⟨ p′ ⟩ W → Diverges W
            → divergences (P □ Q) (e ∷ p′)
□-ev-lift-L P Q {P₁ = P₁} (sVis {v = vP} {at = at} {a = a} eqP brP) rest divW with PTree.force Q in eqQ
... | ret _ = div-ev-prepend (sVis (fL-F {P = P} {Q = Q} eqP eqQ) brP) (mk-div rest divW)
... | sil _ = div-ev-prepend (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                                   (mergeVis-L-eq {vP = vP} {vQ = ∅v} brP refl)) (mk-div rest divW)
... | react vQ τcQ with vQ at a in eqVQ
...   | nothing =
        div-ev-prepend (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                             (mergeVis-L-eq {vP = vP} {vQ = vQ} brP eqVQ)) (mk-div rest divW)
...   | just Q₁ =
        div-ev-prepend (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                             (mergeVis-LQ-eq {vP = vP} {vQ = vQ} brP eqVQ))
                       (div-τ-prepend (⊓-stepL P₁ Q₁) (mk-div rest divW))
□-ev-lift-L P Q (sRet eqP) rest divW with deadlock-⟹-[] rest
... | refl , refl = ⊥-elim (deadlock-converges divW)

-- mirror: lift a right visible/√ step
□-ev-lift-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {Q₁ W : PTree E (ExtI E) R}
              {e : Event√ R} {p′ : List (Event√ R)}
            → Q ─[ ev e ]─► Q₁ → Q₁ ⟹⟨ p′ ⟩ W → Diverges W
            → divergences (P □ Q) (e ∷ p′)
□-ev-lift-R P Q {Q₁ = Q₁} (sVis {v = vQ} {at = at} {a = a} eqQ brQ) rest divW with PTree.force P in eqP
... | ret _ = div-ev-prepend (sVis (fL-D {P = P} {Q = Q} eqP eqQ) brQ) (mk-div rest divW)
... | sil _ = div-ev-prepend (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                                   (mergeVis-R-eq {vP = ∅v} {vQ = vQ} refl brQ)) (mk-div rest divW)
... | react vP τcP with vP at a in eqVP
...   | nothing =
        div-ev-prepend (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                             (mergeVis-R-eq {vP = vP} {vQ = vQ} eqVP brQ)) (mk-div rest divW)
...   | just P₁ =
        div-ev-prepend (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                             (mergeVis-LQ-eq {vP = vP} {vQ = vQ} eqVP brQ))
                       (div-τ-prepend (⊓-stepR P₁ Q₁) (mk-div rest divW))
□-ev-lift-R P Q (sRet eqQ) rest divW with deadlock-⟹-[] rest
... | refl , refl = ⊥-elim (deadlock-converges divW)

-- lift a leading big-step of P (resp. A) into P □ Q (resp. A ▷ Q), reaching a divergence
□-reach-intro-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
                  {p : List (Event√ R)} {W : PTree E (ExtI E) R}
                → P ⟹⟨ p ⟩ W → Diverges W → divergences (P □ Q) p
▷-reach-intro-L : (A Q : PTree E (ExtI E) R)
                  {p : List (Event√ R)} {W : PTree E (ExtI E) R}
                → A ⟹⟨ p ⟩ W → Diverges W → divergences (A ▷ Q) p

□-reach-intro-L P Q ⟹-refl divW = empty-div (□-Diverges-L divW)
□-reach-intro-L P Q (⟹-τ {q = P₁} step rest) divW with PTree.force Q in eqQ
... | ret _    = div-τ-prepend (□-τ-toslide P Q step eqQ) (▷-reach-intro-L P₁ Q rest divW)
... | sil _    = div-τ-prepend (□-τ-tochoice P Q step eqQ tt) (□-reach-intro-L P₁ Q rest divW)
... | react _ _ = div-τ-prepend (□-τ-tochoice P Q step eqQ tt) (□-reach-intro-L P₁ Q rest divW)
□-reach-intro-L P Q (⟹-ev step rest) divW = □-ev-lift-L P Q step rest divW

▷-reach-intro-L A Q ⟹-refl divW = empty-div (▷-Diverges-L divW)
▷-reach-intro-L A Q (⟹-τ {q = A₁} step rest) divW =
  div-τ-prepend (▷-τ-L step) (▷-reach-intro-L A₁ Q rest divW)
▷-reach-intro-L A Q (⟹-ev step rest) divW =
  div-ev-prepend (▷-ev-L {Q = Q} step) (mk-div rest divW)

-- mirror on the right
□-reach-intro-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
                  {p : List (Event√ R)} {W : PTree E (ExtI E) R}
                → Q ⟹⟨ p ⟩ W → Diverges W → divergences (P □ Q) p
□-reach-intro-R P Q ⟹-refl divW = empty-div (□-Diverges-R divW)
□-reach-intro-R P Q (⟹-τ {q = Q₁} step rest) divW with PTree.force P in eqP
... | ret _    = div-τ-prepend (□-τ-toslide-R P Q step eqP) (▷-reach-intro-L Q₁ P rest divW)
... | sil _    = div-τ-prepend (□-τ-tochoice-R P Q step eqP tt) (□-reach-intro-R P Q₁ rest divW)
... | react _ _ = div-τ-prepend (□-τ-tochoice-R P Q step eqP tt) (□-reach-intro-R P Q₁ rest divW)
□-reach-intro-R P Q (⟹-ev step rest) divW = □-ev-lift-R P Q step rest divW

-- divergences P ⊆ divergences (P □ Q)  and  divergences Q ⊆ divergences (P □ Q)
□-div-intro-L : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {s : List (Event√ R)}
              → divergences P s → divergences (P □ Q) s
□-div-intro-L {P = P} {Q = Q} d = subst (divergences (P □ Q)) (sym (d .IsDivergence.split))
  (div-extension-closed (□-reach-intro-L P Q (d .IsDivergence.reach) (d .IsDivergence.divwit)))

□-div-intro-R : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {s : List (Event√ R)}
              → divergences Q s → divergences (P □ Q) s
□-div-intro-R {P = P} {Q = Q} d = subst (divergences (P □ Q)) (sym (d .IsDivergence.split))
  (div-extension-closed (□-reach-intro-R P Q (d .IsDivergence.reach) (d .IsDivergence.divwit)))

-------------------------------------------------------------------------------------
-- Failures ELIMINATION for external choice (the general □ stable-failures law).
-- CONSTRUCTIVE (no König step — that was only for divergence): mirrors □-reach-div
-- with "Diverges W" replaced by "Refuses W X" (= isStable W × refuses).  A ▷-node is
-- never stable, so the ▷ base case is vacuous; the □ refl base extracts the operand
-- failure from a stable P□Q.
-------------------------------------------------------------------------------------

-- the three helpers below are the GENERIC stability facts of `Semantics.Stability`;
-- they are kept here under their historic names (and historic argument order) so that
-- every existing client of `CSP.Laws.FD.ExtChoiceFD` continues to work unchanged.

-- a stable state has no τ-move
stable-no-τ : {t M : PTree E (ExtI E) R} → isStable t → t ─[ τ ]─► M → ⊥
stable-no-τ {t = t} = S.stable-no-τ {t = t}

-- a state whose force is ret is not stable
stable-not-ret : {t : PTree E (ExtI E) R} {r : R} → PTree.force t ≡ ret r → isStable t → ⊥
stable-not-ret {t = t} eqf st = S.stable-not-ret {t = t} st eqf

-- build stability from "the τ-branch function is everywhere nothing"
mk-stable : {t : PTree E (ExtI E) R}
            {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
            {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
          → PTree.force t ≡ react v τc → (∀ i a → τc i a ≡ nothing) → isStable t
mk-stable {t = t} = S.mk-stable {t = t}

-- a ▷-node always has the timeout τ, so it is never stable
▷-unstable : (A B : PTree E (ExtI E) R) → ¬ isStable (A ▷ B)
▷-unstable A B st with PTree.force A | st
... | ret _    | lift ()
... | sil _    | st′ =
      case st′ ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin)
               (lift fzero , lift fzero) of λ ()
... | react _ _ | st′ =
      case st′ ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin)
               (lift fzero , lift fzero) of λ ()

-- failure prependers (rebuild the witness through a leading τ / visible step)
fail-τ-prepend : {P P′ : PTree E (ExtI E) R} {s : List (Event√ R)} {X : Event√ R → Set ℓx}
               → P ─[ τ ]─► P′ → failures P′ s X → failures P s X
fail-τ-prepend step (W , reach , ref) = W , ⟹-τ step reach , ref

fail-ev-prepend : {P P′ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)}
                  {X : Event√ R → Set ℓx}
                → P ─[ ev e ]─► P′ → failures P′ s X → failures P (e ∷ s) X
fail-ev-prepend step (W , reach , ref) = W , ⟹-ev step reach , ref

-- a visible step of P lifts to an offer of P □ Q (when both nodes are react)
□-offers-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
             {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τcP τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
             {e : Event√ R} {M : PTree E (ExtI E) R}
           → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
           → P ─[ ev e ]─► M → Offers (P □ Q) e
□-offers-L P Q eqPx eqQ (sRet eqP) = case trans (sym eqPx) eqP of λ ()
□-offers-L P Q {vQ = vQ} eqPx eqQ (sVis {v = vP} {at = at} {a = a} eqP brP) with vQ at a in eqVQ
... | nothing = _ , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt) (mergeVis-L-eq {vP = vP} {vQ = vQ} brP eqVQ)
... | just Q₁ = _ , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt) (mergeVis-LQ-eq {vP = vP} {vQ = vQ} brP eqVQ)

-- base case: a stable P □ Q's failure is a failure of (either) operand.
-- The `with force P | force Q` reduces `st`'s type (isStable (P□Q)) to the concrete
-- τ-branch shape; every non-(react|react) case has an always-enabled τ there, so `st`
-- instantiated at that index gives `just _ ≡ nothing` (absurd).
□-refl-fail : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {X : Event√ R → Set ℓx}
            → Refuses (P □ Q) X → failures P [] X ⊎ failures Q [] X
□-refl-fail {P = P} {Q = Q} (st , noff) with PTree.force P in eqP | PTree.force Q in eqQ
□-refl-fail {P = P} {Q = Q} (st , noff) | ret rP | ret rQ with rP ≟ rQ
... | yes refl = ⊥-elim (lower st)
... | no ¬eq   = case st (Lift ℓ (Fin 2) , fin) (lift fzero) of λ ()
□-refl-fail {P = P} {Q = Q} (st , noff) | ret rP | sil Q′ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail {P = P} {Q = Q} (st , noff) | ret rP | react vQ τcQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail {P = P} {Q = Q} (st , noff) | sil P′ | ret rQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail {P = P} {Q = Q} (st , noff) | sil P′ | sil Q′ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail {P = P} {Q = Q} (st , noff) | sil P′ | react vQ τcQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail {P = P} {Q = Q} (st , noff) | react vP τcP | ret rQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail {P = P} {Q = Q} (st , noff) | react vP τcP | sil Q′ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift (fsuc fzero) , lift fzero) of λ ()
□-refl-fail {P = P} {Q = Q} {X = X} (st , noff) | react vP τcP | react vQ τcQ =
  inj₁ (P , ⟹-refl , stP , refP)
  where
    pn : ∀ i a → τcP i a ≡ nothing
    pn i a with τcP i a in eqt
    ... | nothing = refl
    ... | just P′ = case trans (sym (□-mt-tag0-eq {nP = react vP τcP} {nQ = react vQ τcQ}
                                                  {P = P} {Q = Q} {iₚ = i} {aₚ = a} {P₁ = P′} eqt))
                               (st ((Lift ℓ (Fin 2) × proj₁ i) , pair fin (proj₂ i)) (lift fzero , a))
                    of λ ()
    stP : isStable P
    stP = mk-stable {t = P} eqP pn
    refP : ∀ e → X e → ¬ Offers P e
    refP e xe (P₁ , pstep) = noff e xe (□-offers-L P Q eqP eqQ pstep)

-- the mutual elimination (recursion on the big-step, exactly as □-reach-div)
□-failures-elim : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
                  {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
                → (P □ Q) ⟹⟨ s ⟩ W → Refuses W X → failures P s X ⊎ failures Q s X
▷-failures-elim : ⦃ _ : DecEq R ⦄ (A B : PTree E (ExtI E) R)
                  {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
                → (A ▷ B) ⟹⟨ s ⟩ W → Refuses W X → failures A s X ⊎ failures B s X

□-failures-elim P Q ⟹-refl ref = □-refl-fail ref
□-failures-elim P Q (⟹-τ step rest) ref with □-τ-elim P Q step
... | cP refl = inj₁ (_ , rest , ref)
... | cQ refl = inj₂ (_ , rest , ref)
... | chP P' Pτ refl with □-failures-elim P' Q rest ref
...   | inj₁ fP' = inj₁ (fail-τ-prepend Pτ fP')
...   | inj₂ fQ  = inj₂ fQ
□-failures-elim P Q (⟹-τ step rest) ref | chQ Q' Qτ refl with □-failures-elim P Q' rest ref
...   | inj₁ fP  = inj₁ fP
...   | inj₂ fQ' = inj₂ (fail-τ-prepend Qτ fQ')
□-failures-elim P Q (⟹-τ step rest) ref | sPQ P' Pτ refl with ▷-failures-elim P' Q rest ref
...   | inj₁ fP' = inj₁ (fail-τ-prepend Pτ fP')
...   | inj₂ fQ  = inj₂ fQ
□-failures-elim P Q (⟹-τ step rest) ref | sQP Q' Qτ refl with ▷-failures-elim Q' P rest ref
...   | inj₁ fQ' = inj₂ (fail-τ-prepend Qτ fQ')
...   | inj₂ fP  = inj₁ fP
□-failures-elim P Q (⟹-ev step rest) ref with □-ev-elim P Q step
... | evP Pev = inj₁ (fail-ev-prepend Pev (_ , rest , ref))
... | evQ Qev = inj₂ (fail-ev-prepend Qev (_ , rest , ref))
... | evPQ {P₁ = P₁} {Q₁ = Q₁} Pev Qev with ⊓-failures→ P₁ Q₁ (_ , rest , ref)
...   | inj₁ fP₁ = inj₁ (fail-ev-prepend Pev fP₁)
...   | inj₂ fQ₁ = inj₂ (fail-ev-prepend Qev fQ₁)

▷-failures-elim A B ⟹-refl ref = ⊥-elim (▷-unstable A B (proj₁ ref))
▷-failures-elim A B (⟹-τ step rest) ref with ▷-τ-elim A B step
... | inj₁ refl              = inj₂ (_ , rest , ref)
... | inj₂ (A' , Aτ , refl) with ▷-failures-elim A' B rest ref
...   | inj₁ fA' = inj₁ (fail-τ-prepend Aτ fA')
...   | inj₂ fB  = inj₂ fB
▷-failures-elim A B (⟹-ev step rest) ref =
  inj₁ (fail-ev-prepend (▷-ev-elim A B step) (_ , rest , ref))

-- top-level failures and failures⊥ elimination
□-failures-elim-top : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
                      {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                    → failures (P □ Q) s X → failures P s X ⊎ failures Q s X
□-failures-elim-top {P = P} {Q = Q} (W , reach , ref) = □-failures-elim P Q reach ref

□-failures⊥-elim : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
                   {s : List (Event√ R)} {B : Event√ R → Set ℓr}
                 → failures⊥ (P □ Q) s B → failures⊥ P s B ⊎ failures⊥ Q s B
□-failures⊥-elim (inj₁ f) with □-failures-elim-top f
... | inj₁ fP = inj₁ (inj₁ fP)
... | inj₂ fQ = inj₂ (inj₁ fQ)
□-failures⊥-elim (inj₂ d) with □-div-elim d
... | inj₁ dP = inj₁ (inj₂ dP)
... | inj₂ dQ = inj₂ (inj₂ dQ)

-------------------------------------------------------------------------------------
-- √-slide bridge: when P terminates (force P ≡ ret r), every failure of the slide
-- Q ▷ P is a failure of P □ Q.  (Only ⊆ holds — NOT a bisimulation: if Q itself can
-- terminate with r''≠r then P□Q = react ∅v(br2) offers both √r,√r'' while Q▷P = ret r''
-- offers only √r''.)  Used by the distribution's `sQP` case (force P = ret).
-------------------------------------------------------------------------------------

-- transfer a τ-step of Q ▷ P to a τ-step of P □ Q reaching the SAME state
slide→□-τ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r : R} {M : PTree E (ExtI E) R}
          → PTree.force P ≡ ret r → (Q ▷ P) ─[ τ ]─► M → (P □ Q) ─[ τ ]─► M
slide→□-τ P Q eqP step with PTree.force Q in eqQ
... | ret r'' = ⊥-elim (ret-no-τ (force-▷-ret {P = Q} {Q = P} eqQ) step)
... | sil Q'' with ▷-τ-elim Q P step
...   | inj₁ refl = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                         {a = lift fzero , lift fzero} (fL-C {P = P} {Q = Q} eqP eqQ) refl
...   | inj₂ (Q' , Qτ , refl) = □-τ-toslide-R P Q Qτ eqP
slide→□-τ P Q eqP step | react vQ τcQ with ▷-τ-elim Q P step
...   | inj₁ refl = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                         {a = lift fzero , lift fzero} (fL-D {P = P} {Q = Q} eqP eqQ) refl
...   | inj₂ (Q' , Qτ , refl) = □-τ-toslide-R P Q Qτ eqP

-- transfer a visible/√ step of Q ▷ P (followed by its continuation) into P □ Q
slide→□-ev : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r : R}
             {e : Event√ R} {M W : PTree E (ExtI E) R} {s : List (Event√ R)}
           → PTree.force P ≡ ret r → (Q ▷ P) ─[ ev e ]─► M → M ⟹⟨ s ⟩ W
           → (P □ Q) ⟹⟨ e ∷ s ⟩ W
slide→□-ev P Q {r = r} eqP step rest with ▷-ev-elim Q P step
... | sVis {at = at} {a = a} eqQv brQ = ⟹-ev (sVis (fL-D {P = P} {Q = Q} eqP eqQv) brQ) rest
... | sRet {x = r''} eqQv with r ≟ r''
...   | yes refl = ⟹-ev (sRet (fL-A {P = P} {Q = Q} eqP eqQv)) rest
...   | no ¬eq   = ⟹-τ (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
                              (fL-B {P = P} {Q = Q} eqP eqQv ¬eq) refl)
                       (⟹-ev (sRet eqQv) rest)

-- a failure of the slide Q ▷ P (P terminated) is a failure of P □ Q
slide-term-fail : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r : R}
                  {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
                → PTree.force P ≡ ret r → (Q ▷ P) ⟹⟨ s ⟩ W → Refuses W X
                → failures (P □ Q) s X
slide-term-fail P Q eqP ⟹-refl (st , _)       = ⊥-elim (▷-unstable Q P st)
slide-term-fail P Q eqP (⟹-τ step rest) ref   = _ , ⟹-τ (slide→□-τ P Q eqP step) rest , ref
slide-term-fail P Q eqP (⟹-ev step rest) ref   = _ , slide→□-ev P Q eqP step rest , ref

-------------------------------------------------------------------------------------
-- Distribution-specific failures elimination: failures(P□(Q⊓S)) factors through
-- P□Q or P□S (the Q⊓S-resolving τ commits to one branch, keeping P paired).
-------------------------------------------------------------------------------------

-- P □ (Q ⊓ S) is never stable (the internal choice always offers a τ)
□-⊓-unstable : ⦃ _ : DecEq R ⦄ (P Q S : PTree E (ExtI E) R) → ¬ isStable (P □ (Q ⊓ S))
□-⊓-unstable P Q S st with PTree.force P | st
... | ret _    | st′ = case st′ ((Lift ℓ (Fin 2) × Lift ℓ (Fin 2)) , pair fin fin)
                                 (lift (fsuc fzero) , lift fzero) of λ ()
... | sil _    | st′ = case st′ ((Lift ℓ (Fin 2) × Lift ℓ (Fin 2)) , pair fin fin)
                                 (lift (fsuc fzero) , lift fzero) of λ ()
... | react _ _ | st′ = case st′ ((Lift ℓ (Fin 2) × Lift ℓ (Fin 2)) , pair fin fin)
                                 (lift (fsuc fzero) , lift fzero) of λ ()

-- P □ Q with Q terminated and P live is never stable (tag0 √-preserve τ)
□-Rret-unstable : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R}
                → NonRet (PTree.force P) → PTree.force Q ≡ ret r′ → ¬ isStable (P □ Q)
□-Rret-unstable P Q ntP eqQ st with PTree.force P | PTree.force Q | ntP | eqQ | st
... | ret _    | _        | () | _  | _
... | sil _    | ret _    | _  | _  | st′ = case st′ ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin)
                                                     (lift fzero , lift fzero) of λ ()
... | react _ _ | ret _    | _  | _  | st′ = case st′ ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin)
                                                     (lift fzero , lift fzero) of λ ()
... | sil _    | sil _    | _  | () | _
... | sil _    | react _ _ | _  | () | _
... | react _ _ | sil _    | _  | () | _
... | react _ _ | react _ _ | _  | () | _

-- inversion of a τ-step of P□Q with Q terminated and P live (mirror of □-slide-RQ):
-- it is the √-preserve to Q (M≡Q) or P's own τ sliding on (M≡P'▷Q)
□-Rret-τ-inv : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R} {M : PTree E (ExtI E) R}
             → NonRet (PTree.force P) → PTree.force Q ≡ ret r′ → (P □ Q) ─[ τ ]─► M
             → (M ≡ Q) ⊎ Σ[ P′ ∈ PTree E (ExtI E) R ] ((P ─[ τ ]─► P′) × (M ≡ P′ ▷ Q))
□-Rret-τ-inv P Q ntP eqQ (sSil eqf) with PTree.force P | PTree.force Q | eqQ | ntP
... | sil _    | _ | refl | _ = case eqf of λ ()
... | react _ _ | _ | refl | _ = case eqf of λ ()
... | ret _    | _ | refl | ()
□-Rret-τ-inv P Q ntP eqQ (sTau {i = i} {a = a} eqf br)
  with PTree.force P in eqP | PTree.force Q | eqQ | ntP
... | sil P₁ | _ | refl | _
      with □-slide-PR-elim (sil P₁) Q {i = i} {a = a} (subst (λ f → f i a ≡ _) (sym (proj₂ (react-injective eqf))) br)
...   | inj₁ m≡Q = inj₁ m≡Q
...   | inj₂ (j , a′ , P′ , veq , m≡) = inj₂ (P′ , viewT-τ eqP veq , m≡)
□-Rret-τ-inv P Q ntP eqQ (sTau {i = i} {a = a} eqf br) | react vP τcP | _ | refl | _
      with □-slide-PR-elim (react vP τcP) Q {i = i} {a = a} (subst (λ f → f i a ≡ _) (sym (proj₂ (react-injective eqf))) br)
...   | inj₁ m≡Q = inj₁ m≡Q
...   | inj₂ (j , a′ , P′ , veq , m≡) = inj₂ (P′ , viewT-τ eqP veq , m≡)
□-Rret-τ-inv P Q ntP eqQ (sTau eqf br) | ret _ | _ | refl | ()

-- transfer a τ-step / visible step of P□Q (P live, Q terminated) to P▷Q (same M)
□→▷-term-step-τ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R} {M : PTree E (ExtI E) R}
                → NonRet (PTree.force P) → PTree.force Q ≡ ret r′
                → (P □ Q) ─[ τ ]─► M → (P ▷ Q) ─[ τ ]─► M
□→▷-term-step-τ P Q ntP eqQ step with □-Rret-τ-inv P Q ntP eqQ step
... | inj₁ refl              = ▷-timeout P Q refl ntP
... | inj₂ (P′ , Pτ , refl)  = ▷-τ-L Pτ

□→▷-term-step-ev : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R}
                   {e : Event√ R} {M : PTree E (ExtI E) R}
                 → NonRet (PTree.force P) → PTree.force Q ≡ ret r′
                 → (P □ Q) ─[ ev e ]─► M → (P ▷ Q) ─[ ev e ]─► M
□→▷-term-step-ev P Q ntP eqQ (sVis {at = at} {a = a} eqf br)
  with PTree.force P in eqP | PTree.force Q | eqQ | ntP
... | react vP τcP | _ | refl | _ =
      ▷-ev-L (sVis eqP (subst (λ f → f at a ≡ _) (sym (proj₁ (react-injective eqf))) br))
... | sil _ | _ | refl | _ =
      case subst (λ f → f at a ≡ _) (sym (proj₁ (react-injective eqf))) br of λ ()
... | ret _ | _ | refl | ()
□→▷-term-step-ev P Q ntP eqQ (sRet eqf) with PTree.force P | PTree.force Q | eqQ | ntP
... | sil _    | _ | refl | _ = case eqf of λ ()
... | react _ _ | _ | refl | _ = case eqf of λ ()
... | ret _    | _ | refl | ()

-- the conversion: failures(P□Q) ⊆ failures(P▷Q) when P live, Q terminated
□→▷-term : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R}
           {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
         → NonRet (PTree.force P) → PTree.force Q ≡ ret r′
         → (P □ Q) ⟹⟨ s ⟩ W → Refuses W X → failures (P ▷ Q) s X
□→▷-term P Q ntP eqQ ⟹-refl (st , _)     = ⊥-elim (□-Rret-unstable P Q ntP eqQ st)
□→▷-term P Q ntP eqQ (⟹-τ step rest) ref = _ , ⟹-τ (□→▷-term-step-τ P Q ntP eqQ step) rest , ref
□→▷-term P Q ntP eqQ (⟹-ev step rest) ref = _ , ⟹-ev (□→▷-term-step-ev P Q ntP eqQ step) rest , ref

-- P □ Q ─τ→ Q : the √-preserve commit when P live, Q terminated (tag0 slide)
□-τ-toQ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R}
        → NonRet (PTree.force P) → PTree.force Q ≡ ret r′ → (P □ Q) ─[ τ ]─► Q
□-τ-toQ P Q ntP eqQ with PTree.force P in eqP | ntP
... | sil _    | _ = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                          {a = lift fzero , lift fzero} (fL-E {P = P} {Q = Q} eqP eqQ) refl
... | react _ _ | _ = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                          {a = lift fzero , lift fzero} (fL-F {P = P} {Q = Q} eqP eqQ) refl
... | ret _    | ()

-- a failure of a terminated A is a failure of A ▷ Q (the √ resolves the slide)
term-fail-▷ : ⦃ _ : DecEq R ⦄ (A Q : PTree E (ExtI E) R) {r′ : R}
              {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
            → PTree.force A ≡ ret r′ → A ⟹⟨ s ⟩ W → Refuses W X → failures (A ▷ Q) s X
term-fail-▷ A Q eqA ⟹-refl (st , _) with PTree.force A | st
... | ret _ | lift ()
term-fail-▷ A Q eqA (⟹-τ (sSil eq) _) _ with PTree.force A
... | ret _ = case trans (sym eqA) eq of λ ()
term-fail-▷ A Q eqA (⟹-τ (sTau eq _) _) _ with PTree.force A
... | ret _ = case trans (sym eqA) eq of λ ()
term-fail-▷ A Q eqA (⟹-ev step rest) ref = _ , ⟹-ev (▷-ev-L step) rest , ref
-- the chP τ-prepend: failures(P′□Q) ⊆ failures(P□Q) when P─[τ]→P′ (P live)
□-fail-τ-pre-L : ⦃ _ : DecEq R ⦄ (P P′ Q : PTree E (ExtI E) R)
                 {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
               → NonRet (PTree.force P) → P ─[ τ ]─► P′ → (P′ □ Q) ⟹⟨ s ⟩ W → Refuses W X
               → failures (P □ Q) s X
□-fail-τ-pre-L P P′ Q ntP step reach′ ref with PTree.force Q in eqQ
... | sil _    = _ , ⟹-τ (□-τ-tochoice P Q step eqQ tt) reach′ , ref
... | react _ _ = _ , ⟹-τ (□-τ-tochoice P Q step eqQ tt) reach′ , ref
... | ret _ with PTree.force P′ in eqP′
...   | sil _ =
        let (W₂ , r₂ , rf₂) = □→▷-term P′ Q (subst NonRet (sym eqP′) tt) eqQ reach′ ref
        in _ , ⟹-τ (□-τ-toslide P Q step eqQ) r₂ , rf₂
...   | react _ _ =
        let (W₂ , r₂ , rf₂) = □→▷-term P′ Q (subst NonRet (sym eqP′) tt) eqQ reach′ ref
        in _ , ⟹-τ (□-τ-toslide P Q step eqQ) r₂ , rf₂
...   | ret _ with □-failures-elim-top {P = P′} {Q = Q} (_ , reach′ , ref)
...     | inj₁ fP′ =
          let (W₂ , r₂ , rf₂) = term-fail-▷ P′ Q eqP′ (proj₁ (proj₂ fP′)) (proj₂ (proj₂ fP′))
          in _ , ⟹-τ (□-τ-toslide P Q step eqQ) r₂ , rf₂
...     | inj₂ fQ  = _ , ⟹-τ (□-τ-toQ P Q ntP eqQ) (proj₁ (proj₂ fQ)) , proj₂ (proj₂ fQ)

-- custom τ-inversion for P □ (Q ⊓ S): the 2nd operand is always react/nonret, so the
-- four shapes carry the force-P info that the generic □-τ-elim drops.
□-⊓-τ-inv : ⦃ _ : DecEq R ⦄ (P Q S : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
          → (P □ (Q ⊓ S)) ─[ τ ]─► M
          → (Σ[ P′ ∈ PTree E (ExtI E) R ] ((P ─[ τ ]─► P′) × (M ≡ P′ □ (Q ⊓ S))))
          ⊎ (Σ[ Q″ ∈ PTree E (ExtI E) R ] (((Q ⊓ S) ─[ τ ]─► Q″) × (M ≡ P □ Q″)))
          ⊎ (Σ[ r ∈ R ] ((PTree.force P ≡ ret r) × (M ≡ P)))
          ⊎ (Σ[ Q″ ∈ PTree E (ExtI E) R ] Σ[ r ∈ R ]
               (((Q ⊓ S) ─[ τ ]─► Q″) × (PTree.force P ≡ ret r) × (M ≡ Q″ ▷ P)))
□-⊓-τ-inv P Q S (sSil eqf) with PTree.force P
... | ret _    = case eqf of λ ()
... | sil _    = case eqf of λ ()
... | react _ _ = case eqf of λ ()
□-⊓-τ-inv P Q S (sTau {i = i} {a = a} eqf br) with PTree.force P in eqP
... | ret r
      with □-slide-RQ-elim P (react ∅v (br2 Q S)) {i = i} {a = a}
             (subst (λ f → f i a ≡ _) (sym (proj₂ (react-injective eqf))) br)
...   | inj₁ m≡P                    = inj₂ (inj₂ (inj₁ (r , refl , m≡P)))
...   | inj₂ (j , a′ , Q′ , veq , m≡) = inj₂ (inj₂ (inj₂ (Q′ , r , viewT-τ {j = j} {a' = a′} refl veq , refl , m≡)))
□-⊓-τ-inv P Q S (sTau {i = i} {a = a} eqf br) | sil P₁
      with □-mt-elim (sil P₁) (react ∅v (br2 Q S)) P (Q ⊓ S) {i = i} {a = a}
             (subst (λ f → f i a ≡ _) (sym (proj₂ (react-injective eqf))) br)
...   | inj₁ (j , a′ , P′ , veq , m≡) = inj₁ (P′ , viewT-τ {j = j} {a' = a′} eqP veq , m≡)
...   | inj₂ (j , a′ , Q′ , veq , m≡) = inj₂ (inj₁ (Q′ , viewT-τ {j = j} {a' = a′} refl veq , m≡))
□-⊓-τ-inv P Q S (sTau {i = i} {a = a} eqf br) | react vP τcP
      with □-mt-elim (react vP τcP) (react ∅v (br2 Q S)) P (Q ⊓ S) {i = i} {a = a}
             (subst (λ f → f i a ≡ _) (sym (proj₂ (react-injective eqf))) br)
...   | inj₁ (j , a′ , P′ , veq , m≡) = inj₁ (P′ , viewT-τ {j = j} {a' = a′} eqP veq , m≡)
...   | inj₂ (j , a′ , Q′ , veq , m≡) = inj₂ (inj₁ (Q′ , viewT-τ {j = j} {a' = a′} refl veq , m≡))

-- P's visible/√ step lifts into P □ Q reaching the SAME final state (W explicit,
-- unlike □-ev-L which returns a traces Σ).  Mirrors □-ev-L.
□-ev-toL : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {P₁ W : PTree E (ExtI E) R}
           {e : Event√ R} {s : List (Event√ R)}
         → P ─[ ev e ]─► P₁ → P₁ ⟹⟨ s ⟩ W → (P □ Q) ⟹⟨ e ∷ s ⟩ W
□-ev-toL P Q {P₁ = P₁} (sVis {v = vP} {at = at} {a = a} eqP brP) rest with PTree.force Q in eqQ
... | ret _ = ⟹-ev (sVis (fL-F {P = P} {Q = Q} eqP eqQ) brP) rest
... | sil _ = ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                         (mergeVis-L-eq {vP = vP} {vQ = ∅v} brP refl)) rest
... | react vQ τcQ with vQ at a in eqVQ
...   | nothing = ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                             (mergeVis-L-eq {vP = vP} {vQ = vQ} brP eqVQ)) rest
...   | just Q₁ = ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                             (mergeVis-LQ-eq {vP = vP} {vQ = vQ} brP eqVQ)) (⟹-τ (⊓-stepL P₁ Q₁) rest)
□-ev-toL P Q (sRet {x = x} eqP) rest with PTree.force Q in eqQ
... | ret r′ with x ≟ r′
...   | yes refl = ⟹-ev (sRet (fL-A {P = P} {Q = Q} eqP eqQ)) rest
...   | no ¬eq   = ⟹-τ (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero}
                             (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) refl) (⟹-ev (sRet eqP) rest)
□-ev-toL P Q (sRet {x = x} eqP) rest | sil _ =
  ⟹-τ (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
            {a = lift fzero , lift fzero} (fL-C {P = P} {Q = Q} eqP eqQ) refl)
      (⟹-ev (sRet eqP) rest)
□-ev-toL P Q (sRet {x = x} eqP) rest | react _ _ =
  ⟹-τ (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
            {a = lift fzero , lift fzero} (fL-D {P = P} {Q = Q} eqP eqQ) refl)
      (⟹-ev (sRet eqP) rest)

-- a τ-step's source is non-terminated
τ→NonRet : {P P′ : PTree E (ExtI E) R} → P ─[ τ ]─► P′ → NonRet (PTree.force P)
τ→NonRet (sSil eq)   = subst NonRet (sym eq) tt
τ→NonRet (sTau eq _) = subst NonRet (sym eq) tt

-- an internal choice offers no visible event
⊓-no-ev : ⦃ _ : DecEq R ⦄ {Q S : PTree E (ExtI E) R} {e : Event√ R} {M : PTree E (ExtI E) R}
        → (Q ⊓ S) ─[ ev e ]─► M → ⊥
⊓-no-ev (sRet eq)    = case eq of λ ()
⊓-no-ev (sVis eq br) with react-injective eq
... | refl , _ = case br of λ ()

-- DISTRIBUTION-specific failures elimination: failures(P□(Q⊓S)) factors through
-- P□Q or P□S (the Q⊓S-resolving τ commits to a branch, keeping P paired).
□-⊓-fail-elim : ⦃ _ : DecEq R ⦄ (P Q S : PTree E (ExtI E) R)
                {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
              → (P □ (Q ⊓ S)) ⟹⟨ s ⟩ W → Refuses W X
              → failures (P □ Q) s X ⊎ failures (P □ S) s X
□-⊓-fail-elim P Q S ⟹-refl ref = ⊥-elim (□-⊓-unstable P Q S (proj₁ ref))
□-⊓-fail-elim P Q S (⟹-τ step rest) ref with □-⊓-τ-inv P Q S step
... | inj₁ (P′ , Pτ , refl) with □-⊓-fail-elim P′ Q S rest ref
...   | inj₁ (W₂ , r₂ , rf₂) = inj₁ (□-fail-τ-pre-L P P′ Q (τ→NonRet Pτ) Pτ r₂ rf₂)
...   | inj₂ (W₂ , r₂ , rf₂) = inj₂ (□-fail-τ-pre-L P P′ S (τ→NonRet Pτ) Pτ r₂ rf₂)
□-⊓-fail-elim P Q S (⟹-τ step rest) ref | inj₂ (inj₁ (Q″ , Q⊓Sτ , refl)) with ⊓-τ-inv Q S Q⊓Sτ
...   | inj₁ refl = inj₁ (_ , rest , ref)
...   | inj₂ refl = inj₂ (_ , rest , ref)
□-⊓-fail-elim P Q S (⟹-τ step rest) ref | inj₂ (inj₂ (inj₁ (r , eqP , refl))) with rest
...   | ⟹-refl            = ⊥-elim (stable-not-ret {t = P} eqP (proj₁ ref))
...   | ⟹-τ step′ _       = ⊥-elim (ret-no-τ eqP step′)
...   | ⟹-ev step′ rest′  = inj₁ (_ , □-ev-toL P Q step′ rest′ , ref)
□-⊓-fail-elim P Q S (⟹-τ step rest) ref | inj₂ (inj₂ (inj₂ (Q″ , r , Q⊓Sτ , eqP , refl)))
  with ⊓-τ-inv Q S Q⊓Sτ
...   | inj₁ refl = inj₁ (slide-term-fail P Q eqP rest ref)
...   | inj₂ refl = inj₂ (slide-term-fail P S eqP rest ref)
□-⊓-fail-elim P Q S (⟹-ev step rest) ref with □-ev-elim P (Q ⊓ S) step
... | evP Pev = inj₁ (_ , □-ev-toL P Q Pev rest , ref)
□-⊓-fail-elim P Q S (⟹-ev step rest) ref | evQ Qev = ⊥-elim (⊓-no-ev Qev)
□-⊓-fail-elim P Q S (⟹-ev step rest) ref | evPQ _ Qev = ⊥-elim (⊓-no-ev Qev)

-- distribution-specific divergence elim (combines □-div-elim/intro + ⊓-div→)
□-⊓-div-elim : ⦃ _ : DecEq R ⦄ {P Q S : PTree E (ExtI E) R} {s : List (Event√ R)}
             → divergences (P □ (Q ⊓ S)) s → divergences (P □ Q) s ⊎ divergences (P □ S) s
□-⊓-div-elim {P = P} {Q = Q} {S = S} d with □-div-elim {P = P} {Q = Q ⊓ S} d
... | inj₁ dP  = inj₁ (□-div-intro-L dP)
... | inj₂ dQS with ⊓-div→ Q S dQS
...   | inj₁ dQ = inj₁ (□-div-intro-R dQ)
...   | inj₂ dS = inj₂ (□-div-intro-R dS)

-- ⊒ direction: (P□Q)⊓(P□S) ⊑FD P□(Q⊓S)  (failures/divergences of P□(Q⊓S) factor)
□-⊓-dist-⊒ : ⦃ _ : DecEq R ⦄ (P Q S : PTree E (ExtI E) R)
           → ((P □ Q) ⊓ (P □ S)) ⊑FD (P □ (Q ⊓ S))
□-⊓-dist-⊒ P Q S = f⊥ , fd
  where
    f⊥ : ((P □ Q) ⊓ (P □ S)) ⊇F⊥ (P □ (Q ⊓ S))
    f⊥ (inj₁ (W , reach , ref)) with □-⊓-fail-elim P Q S reach ref
    ... | inj₁ fPQ = ⊓-failures⊥←l (P □ Q) (P □ S) (inj₁ fPQ)
    ... | inj₂ fPS = ⊓-failures⊥←r (P □ Q) (P □ S) (inj₁ fPS)
    f⊥ (inj₂ d) with □-⊓-div-elim d
    ... | inj₁ dPQ = ⊓-failures⊥←l (P □ Q) (P □ S) (inj₂ dPQ)
    ... | inj₂ dPS = ⊓-failures⊥←r (P □ Q) (P □ S) (inj₂ dPS)
    fd : ((P □ Q) ⊓ (P □ S)) ⊇D (P □ (Q ⊓ S))
    fd d with □-⊓-div-elim d
    ... | inj₁ dPQ = ⊓-div←l (P □ Q) (P □ S) dPQ
    ... | inj₂ dPS = ⊓-div←r (P □ Q) (P □ S) dPS

-- distribution divergence INTRO: divergences(P□Q) ⊆ divergences(P□(Q⊓S))
□-⊓-div-intro-L : ⦃ _ : DecEq R ⦄ {P Q S : PTree E (ExtI E) R} {s : List (Event√ R)}
                → divergences (P □ Q) s → divergences (P □ (Q ⊓ S)) s
□-⊓-div-intro-L {P = P} {Q = Q} {S = S} d with □-div-elim {P = P} {Q = Q} d
... | inj₁ dP = □-div-intro-L {P = P} {Q = Q ⊓ S} dP
... | inj₂ dQ = □-div-intro-R {P = P} {Q = Q ⊓ S} (⊓-div←l Q S dQ)

□-⊓-div-intro-R : ⦃ _ : DecEq R ⦄ {P Q S : PTree E (ExtI E) R} {s : List (Event√ R)}
                → divergences (P □ S) s → divergences (P □ (Q ⊓ S)) s
□-⊓-div-intro-R {P = P} {Q = Q} {S = S} d with □-div-elim {P = P} {Q = S} d
... | inj₁ dP = □-div-intro-L {P = P} {Q = Q ⊓ S} dP
... | inj₂ dS = □-div-intro-R {P = P} {Q = Q ⊓ S} (⊓-div←r Q S dS)

-- mirror of □-Rret-unstable: P □ Q with P terminated and Q live is never stable
□-Lret-unstable : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R}
                → PTree.force P ≡ ret r′ → NonRet (PTree.force Q) → ¬ isStable (P □ Q)
□-Lret-unstable P Q eqP ntQ st with PTree.force P | PTree.force Q | eqP | ntQ | st
... | ret _    | sil _    | _ | _  | st′ = case st′ ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin)
                                                     (lift fzero , lift fzero) of λ ()
... | ret _    | react _ _ | _ | _  | st′ = case st′ ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin)
                                                     (lift fzero , lift fzero) of λ ()
... | ret _    | ret _    | _ | () | _
... | sil _    | _        | () | _ | _
... | react _ _ | _        | () | _ | _

-- mirror of □-Rret-τ-inv: P terminated, Q live ⇒ √-preserve to P (M≡P) or Q's slide
□-Lret-τ-inv : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R} {M : PTree E (ExtI E) R}
             → PTree.force P ≡ ret r′ → NonRet (PTree.force Q) → (P □ Q) ─[ τ ]─► M
             → (M ≡ P) ⊎ Σ[ Q′ ∈ PTree E (ExtI E) R ] ((Q ─[ τ ]─► Q′) × (M ≡ Q′ ▷ P))
□-Lret-τ-inv P Q eqP ntQ (sSil eqf) with PTree.force P | PTree.force Q | eqP | ntQ
... | ret _    | sil _    | _ | _  = case eqf of λ ()
... | ret _    | react _ _ | _ | _  = case eqf of λ ()
... | ret _    | ret _    | _ | ()
... | sil _    | _        | () | _
... | react _ _ | _        | () | _
□-Lret-τ-inv P Q eqP ntQ (sTau {i = i} {a = a} eqf br) with PTree.force Q in eqQ | PTree.force P | eqP | ntQ
... | sil Q₁ | ret _ | refl | _
      with □-slide-RQ-elim P (sil Q₁) {i = i} {a = a} (subst (λ f → f i a ≡ _) (sym (proj₂ (react-injective eqf))) br)
...   | inj₁ m≡P                    = inj₁ m≡P
...   | inj₂ (j , a′ , Q′ , veq , m≡) = inj₂ (Q′ , viewT-τ {j = j} {a' = a′} eqQ veq , m≡)
□-Lret-τ-inv P Q eqP ntQ (sTau {i = i} {a = a} eqf br) | react vQ τcQ | ret _ | refl | _
      with □-slide-RQ-elim P (react vQ τcQ) {i = i} {a = a} (subst (λ f → f i a ≡ _) (sym (proj₂ (react-injective eqf))) br)
...   | inj₁ m≡P                    = inj₁ m≡P
...   | inj₂ (j , a′ , Q′ , veq , m≡) = inj₂ (Q′ , viewT-τ {j = j} {a' = a′} eqQ veq , m≡)
□-Lret-τ-inv P Q eqP ntQ (sTau eqf br) | ret _ | _ | refl | ()

□→▷-Pret-step-τ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R} {M : PTree E (ExtI E) R}
                → PTree.force P ≡ ret r′ → NonRet (PTree.force Q)
                → (P □ Q) ─[ τ ]─► M → (Q ▷ P) ─[ τ ]─► M
□→▷-Pret-step-τ P Q eqP ntQ step with □-Lret-τ-inv P Q eqP ntQ step
... | inj₁ refl              = ▷-timeout Q P refl ntQ
... | inj₂ (Q′ , Qτ , refl)  = ▷-τ-L Qτ

□→▷-Pret-step-ev : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R}
                   {e : Event√ R} {M : PTree E (ExtI E) R}
                 → PTree.force P ≡ ret r′ → NonRet (PTree.force Q)
                 → (P □ Q) ─[ ev e ]─► M → (Q ▷ P) ─[ ev e ]─► M
□→▷-Pret-step-ev P Q eqP ntQ (sVis {at = at} {a = a} eqf br)
  with PTree.force Q in eqQ | PTree.force P | eqP | ntQ
... | react vQ τcQ | ret _ | refl | _ =
      ▷-ev-L (sVis eqQ (subst (λ f → f at a ≡ _) (sym (proj₁ (react-injective eqf))) br))
... | sil _ | ret _ | refl | _ =
      case subst (λ f → f at a ≡ _) (sym (proj₁ (react-injective eqf))) br of λ ()
... | ret _ | _ | refl | ()
□→▷-Pret-step-ev P Q eqP ntQ (sRet eqf) with PTree.force P | PTree.force Q | eqP | ntQ
... | ret _    | sil _    | _ | _  = case eqf of λ ()
... | ret _    | react _ _ | _ | _  = case eqf of λ ()
... | ret _    | ret _    | _ | ()
... | sil _    | _        | () | _
... | react _ _ | _        | () | _

-- failures(P□Q) ⊆ failures(Q▷P) when P terminated, Q live (mirror of □→▷-term)
□→▷-Pret : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R}
           {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
         → PTree.force P ≡ ret r′ → NonRet (PTree.force Q)
         → (P □ Q) ⟹⟨ s ⟩ W → Refuses W X → failures (Q ▷ P) s X
□→▷-Pret P Q eqP ntQ ⟹-refl (st , _)     = ⊥-elim (□-Lret-unstable P Q eqP ntQ st)
□→▷-Pret P Q eqP ntQ (⟹-τ step rest) ref = _ , ⟹-τ (□→▷-Pret-step-τ P Q eqP ntQ step) rest , ref
□→▷-Pret P Q eqP ntQ (⟹-ev step rest) ref = _ , ⟹-ev (□→▷-Pret-step-ev P Q eqP ntQ step) rest , ref

-- P □ Q ─τ→ P : the √-preserve when P terminated, Q live (tag0; mirror of □-τ-toQ)
□-τ-toP : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r′ : R}
        → PTree.force P ≡ ret r′ → NonRet (PTree.force Q) → (P □ Q) ─[ τ ]─► P
□-τ-toP P Q eqP ntQ with PTree.force Q in eqQ | PTree.force P | eqP | ntQ
... | sil _    | ret _ | refl | _ = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                                         {a = lift fzero , lift fzero} (fL-C {P = P} {Q = Q} eqP eqQ) refl
... | react _ _ | ret _ | refl | _ = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                                         {a = lift fzero , lift fzero} (fL-D {P = P} {Q = Q} eqP eqQ) refl
... | ret _    | _     | _    | ()

-- failures INTRO: failures(P□Q) ⊆ failures(P□(Q⊓S))  (resolving τ + the √-mirror)
□-⊓-fail-intro-L : ⦃ _ : DecEq R ⦄ (P Q S : PTree E (ExtI E) R)
                   {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
                 → (P □ Q) ⟹⟨ s ⟩ W → Refuses W X → failures (P □ (Q ⊓ S)) s X
□-⊓-fail-intro-L P Q S reach ref with PTree.force P in eqP
... | sil _    = _ , ⟹-τ (□-τ-tochoice-R P (Q ⊓ S) (⊓-stepL Q S) eqP tt) reach , ref
... | react _ _ = _ , ⟹-τ (□-τ-tochoice-R P (Q ⊓ S) (⊓-stepL Q S) eqP tt) reach , ref
... | ret _ with PTree.force Q in eqQ
...   | sil _ =
        let (W₂ , r₂ , rf₂) = □→▷-Pret P Q eqP (subst NonRet (sym eqQ) tt) reach ref
        in _ , ⟹-τ (□-τ-toslide-R P (Q ⊓ S) (⊓-stepL Q S) eqP) r₂ , rf₂
...   | react _ _ =
        let (W₂ , r₂ , rf₂) = □→▷-Pret P Q eqP (subst NonRet (sym eqQ) tt) reach ref
        in _ , ⟹-τ (□-τ-toslide-R P (Q ⊓ S) (⊓-stepL Q S) eqP) r₂ , rf₂
...   | ret _ with □-failures-elim-top {P = P} {Q = Q} (_ , reach , ref)
...     | inj₁ fP = _ , ⟹-τ (□-τ-toP P (Q ⊓ S) eqP tt) (proj₁ (proj₂ fP)) , proj₂ (proj₂ fP)
...     | inj₂ fQ =
          let (W₂ , r₂ , rf₂) = term-fail-▷ Q P eqQ (proj₁ (proj₂ fQ)) (proj₂ (proj₂ fQ))
          in _ , ⟹-τ (□-τ-toslide-R P (Q ⊓ S) (⊓-stepL Q S) eqP) r₂ , rf₂

□-⊓-fail-intro-R : ⦃ _ : DecEq R ⦄ (P Q S : PTree E (ExtI E) R)
                   {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
                 → (P □ S) ⟹⟨ s ⟩ W → Refuses W X → failures (P □ (Q ⊓ S)) s X
□-⊓-fail-intro-R P Q S reach ref with PTree.force P in eqP
... | sil _    = _ , ⟹-τ (□-τ-tochoice-R P (Q ⊓ S) (⊓-stepR Q S) eqP tt) reach , ref
... | react _ _ = _ , ⟹-τ (□-τ-tochoice-R P (Q ⊓ S) (⊓-stepR Q S) eqP tt) reach , ref
... | ret _ with PTree.force S in eqS
...   | sil _ =
        let (W₂ , r₂ , rf₂) = □→▷-Pret P S eqP (subst NonRet (sym eqS) tt) reach ref
        in _ , ⟹-τ (□-τ-toslide-R P (Q ⊓ S) (⊓-stepR Q S) eqP) r₂ , rf₂
...   | react _ _ =
        let (W₂ , r₂ , rf₂) = □→▷-Pret P S eqP (subst NonRet (sym eqS) tt) reach ref
        in _ , ⟹-τ (□-τ-toslide-R P (Q ⊓ S) (⊓-stepR Q S) eqP) r₂ , rf₂
...   | ret _ with □-failures-elim-top {P = P} {Q = S} (_ , reach , ref)
...     | inj₁ fP = _ , ⟹-τ (□-τ-toP P (Q ⊓ S) eqP tt) (proj₁ (proj₂ fP)) , proj₂ (proj₂ fP)
...     | inj₂ fS =
          let (W₂ , r₂ , rf₂) = term-fail-▷ S P eqS (proj₁ (proj₂ fS)) (proj₂ (proj₂ fS))
          in _ , ⟹-τ (□-τ-toslide-R P (Q ⊓ S) (⊓-stepR Q S) eqP) r₂ , rf₂

-- ⊑ direction: P□(Q⊓S) ⊑FD (P□Q)⊓(P□S)
□-⊓-dist-⊑ : ⦃ _ : DecEq R ⦄ (P Q S : PTree E (ExtI E) R)
           → (P □ (Q ⊓ S)) ⊑FD ((P □ Q) ⊓ (P □ S))
□-⊓-dist-⊑ P Q S = f⊥ , fd
  where
    f⊥ : (P □ (Q ⊓ S)) ⊇F⊥ ((P □ Q) ⊓ (P □ S))
    f⊥ fb with ⊓-failures⊥→ (P □ Q) (P □ S) fb
    ... | inj₁ (inj₁ (W , reach , ref)) = inj₁ (□-⊓-fail-intro-L P Q S reach ref)
    ... | inj₁ (inj₂ dPQ)               = inj₂ (□-⊓-div-intro-L dPQ)
    ... | inj₂ (inj₁ (W , reach , ref)) = inj₁ (□-⊓-fail-intro-R P Q S reach ref)
    ... | inj₂ (inj₂ dPS)               = inj₂ (□-⊓-div-intro-R dPS)
    fd : (P □ (Q ⊓ S)) ⊇D ((P □ Q) ⊓ (P □ S))
    fd db with ⊓-div→ (P □ Q) (P □ S) db
    ... | inj₁ dPQ = □-⊓-div-intro-L dPQ
    ... | inj₂ dPS = □-⊓-div-intro-R dPS

-- THE LAW: external choice distributes over internal choice (FD-equality)
□-⊓-dist-FD : ⦃ _ : DecEq R ⦄ (P Q S : PTree E (ExtI E) R)
            → (P □ (Q ⊓ S)) ≈FD ((P □ Q) ⊓ (P □ S))
□-⊓-dist-FD P Q S = □-⊓-dist-⊑ P Q S , □-⊓-dist-⊒ P Q S
