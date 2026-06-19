{-# OPTIONS --guardedness #-}

-- Parallel divergence: the foundational divergence lemmas for the parallel FD laws.
--
--   • Par-Diverges→ : Diverges (Par P Q) → Diverges P ⊎ Diverges Q  — the König step,
--     POSTULATED here (mirror of □-/▷-Diverges→ in ExtChoiceDivergence).  CERTIFIED sound
--     from the single `dne` in ClassicalFromLEM (Derivation 5, `Par-no-inf` — a DAcc
--     well-founded recursion: a τ of Par P Q is τL/τR, so the chain stays in Par form and
--     an infinite τ-chain forces an infinite one in P or Q).
--   • Par-Diverges-L / -R : an operand's divergence lifts to the composite — CONSTRUCTIVE
--     (coinductive, the operand's τ's threaded through Par-τ-L / Par-τ-R).
--   • brBoth-Diverges→ : a divergence of the both-offer overlap node is a divergence of one
--     of its two commit branches — CONSTRUCTIVE (one step + brBoth-τ-elim).

open import Level using (Level)
open import Data.Maybe using (Maybe; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FD.ParallelDivergence {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges; deadlock-converges; deadlock-no-τ)
open import Semantics.Refusals {E = E} {I = ExtI E} using (deadlock-no-offer)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (divergences; IsDivergence; empty-div)
open import CSP.Laws.Traces.TraceLawsParallel      E-≟ using (Mg; Par-τ-L; Par-τ-R; Par-sync)
open import CSP.Laws.Traces.TraceLawsParallelMono  E-≟ using (Par-soloL-reach; Par-soloR-reach)
open import CSP.Laws.Traces.TraceLawsParallelElim  E-≟
  using (ParτR; τL; τR; Par-τ-elim; ParevR; evSync; evL; evR; evBoth; ev√; Par-ev-elim)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; brBoth-τ-elim)
open EventSet

private
  variable
    ℓ₁ ℓ₂ ℓs : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓs

-------------------------------------------------------------------------------------
-- the König step (postulated, certified from dne later — like □-/▷-Diverges→)
-------------------------------------------------------------------------------------
postulate
  Par-Diverges→ : (A : EventSet) (merge : Mg R₁ R₂ R)
                  {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
                → Diverges (Par A merge P Q) → Diverges P ⊎ Diverges Q

-------------------------------------------------------------------------------------
-- constructive divergence lifting (no König): an operand's livelock is the composite's
-------------------------------------------------------------------------------------
Par-Diverges-L : (A : EventSet) (merge : Mg R₁ R₂ R)
                 {P : PTree E (ExtI E) R₁} (Q : PTree E (ExtI E) R₂)
               → Diverges P → Diverges (Par A merge P Q)
Par-Diverges-L A merge Q d .Diverges.next =
  Par A merge (d .Diverges.next) Q
Par-Diverges-L A merge {P = P} Q d .Diverges.step =
  Par-τ-L A merge P Q (d .Diverges.step)
Par-Diverges-L A merge Q d .Diverges.rest =
  Par-Diverges-L A merge Q (d .Diverges.rest)

Par-Diverges-R : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) {Q : PTree E (ExtI E) R₂}
               → Diverges Q → Diverges (Par A merge P Q)
Par-Diverges-R A merge P d .Diverges.next =
  Par A merge P (d .Diverges.next)
Par-Diverges-R A merge P {Q = Q} d .Diverges.step =
  Par-τ-R A merge P Q (d .Diverges.step)
Par-Diverges-R A merge P d .Diverges.rest =
  Par-Diverges-R A merge P (d .Diverges.rest)

-------------------------------------------------------------------------------------
-- the both-offer overlap node diverges ⇒ one of its commit branches diverges
-------------------------------------------------------------------------------------
brBoth-Diverges→ : (A : EventSet) (merge : Mg R₁ R₂ R)
                   (P P' : PTree E (ExtI E) R₁) (Q Q' : PTree E (ExtI E) R₂)
                 → Diverges (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P' Q')))
                 → Diverges (Par A merge P' Q) ⊎ Diverges (Par A merge P Q')
brBoth-Diverges→ A merge P P' Q Q' d
  with brBoth-τ-elim A merge P Q P' Q' (d .Diverges.step)
... | inj₁ e = inj₁ (subst Diverges e (d .Diverges.rest))
... | inj₂ e = inj₂ (subst Diverges e (d .Diverges.rest))

-------------------------------------------------------------------------------------
-- DIVERGENCE DECOMPOSITION (elim): a divergence of Par P Q decomposes into a divergence
-- of one operand at a DE-INTERLEAVED sub-trace, with the other operand's trace, related
-- by ParInter.  Mirrors □-reach-div, but threads the interleaving witness; the both-offer
-- overlap node is handled by the mutual Par-ov-reach-div.
-------------------------------------------------------------------------------------
ParDivOut : (A : EventSet) (merge : Mg R₁ R₂ R)
            (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂) (pre : List (Event√ R)) → Set _
ParDivOut {R₁ = R₁} {R₂ = R₂} A merge P Q pre =
  Σ[ sP ∈ List (Event√ R₁) ] Σ[ sQ ∈ List (Event√ R₂) ]
  Σ[ P* ∈ PTree E (ExtI E) R₁ ] Σ[ Q* ∈ PTree E (ExtI E) R₂ ]
    (P ⟹⟨ sP ⟩ P*) × (Q ⟹⟨ sQ ⟩ Q*) × ParInter A merge sP sQ pre × (Diverges P* ⊎ Diverges Q*)

Par-reach-div : (A : EventSet) (merge : Mg R₁ R₂ R)
                (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
              → (Par A merge P Q) ⟹⟨ pre ⟩ W → Diverges W → ParDivOut A merge P Q pre
Par-ov-reach-div : (A : EventSet) (merge : Mg R₁ R₂ R)
                   (P P' : PTree E (ExtI E) R₁) (Q Q' : PTree E (ExtI E) R₂)
                   {X : Set ℓ} {e : E X} {a : X} {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
                 → ¬ A .mem (X , e) a
                 → P ─[ ev (evl (evLabel X e a)) ]─► P'
                 → Q ─[ ev (evl (evLabel X e a)) ]─► Q'
                 → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P' Q'))) ⟹⟨ pre ⟩ W → Diverges W
                 → ParDivOut A merge P Q (evl (evLabel X e a) ∷ pre)

Par-reach-div A merge P Q ⟹-refl divW with Par-Diverges→ A merge divW
... | inj₁ dP = [] , [] , P , Q , ⟹-refl , ⟹-refl , pnil , inj₁ dP
... | inj₂ dQ = [] , [] , P , Q , ⟹-refl , ⟹-refl , pnil , inj₂ dQ
Par-reach-div A merge P Q (⟹-τ step rest) divW with Par-τ-elim A merge P Q step
... | τL P' Pτ refl with Par-reach-div A merge P' Q rest divW
...   | sP , sQ , P* , Q* , rP , rQ , inter , dd = sP , sQ , P* , Q* , ⟹-τ Pτ rP , rQ , inter , dd
Par-reach-div A merge P Q (⟹-τ step rest) divW | τR Q' Qτ refl
  with Par-reach-div A merge P Q' rest divW
...   | sP , sQ , P* , Q* , rP , rQ , inter , dd = sP , sQ , P* , Q* , rP , ⟹-τ Qτ rQ , inter , dd
Par-reach-div A merge P Q (⟹-ev step rest) divW with Par-ev-elim A merge P Q step
... | evSync csat Pev Qev with Par-reach-div A merge _ _ rest divW
...   | sP , sQ , P* , Q* , rP , rQ , inter , dd =
        _ ∷ sP , _ ∷ sQ , P* , Q* , ⟹-ev Pev rP , ⟹-ev Qev rQ , psync csat inter , dd
Par-reach-div A merge P Q (⟹-ev step rest) divW | evL ¬cs Pev
  with Par-reach-div A merge _ Q rest divW
...   | sP , sQ , P* , Q* , rP , rQ , inter , dd =
        _ ∷ sP , sQ , P* , Q* , ⟹-ev Pev rP , rQ , psoloL ¬cs inter , dd
Par-reach-div A merge P Q (⟹-ev step rest) divW | evR ¬cs Qev
  with Par-reach-div A merge P _ rest divW
...   | sP , sQ , P* , Q* , rP , rQ , inter , dd =
        sP , _ ∷ sQ , P* , Q* , rP , ⟹-ev Qev rQ , psoloR ¬cs inter , dd
Par-reach-div A merge P Q (⟹-ev step rest) divW | evBoth ¬cs Pev Qev =
  Par-ov-reach-div A merge P _ Q _ ¬cs Pev Qev rest divW
Par-reach-div A merge P Q (⟹-ev step rest) divW | ev√ fpP fpQ with rest
...   | ⟹-refl        = ⊥-elim (deadlock-converges divW)
...   | ⟹-τ step′ _   = ⊥-elim (deadlock-no-τ step′)
...   | ⟹-ev step′ _  = ⊥-elim (deadlock-no-offer step′)

Par-ov-reach-div A merge P P' Q Q' ¬cs Pev Qev ⟹-refl divW
  with brBoth-Diverges→ A merge P P' Q Q' divW
... | inj₁ dPQ with Par-Diverges→ A merge dPQ
...   | inj₁ dP' = _ ∷ [] , [] , P' , Q , ⟹-ev Pev ⟹-refl , ⟹-refl , psoloL ¬cs pnil , inj₁ dP'
...   | inj₂ dQ  = _ ∷ [] , [] , P' , Q , ⟹-ev Pev ⟹-refl , ⟹-refl , psoloL ¬cs pnil , inj₂ dQ
Par-ov-reach-div A merge P P' Q Q' ¬cs Pev Qev ⟹-refl divW | inj₂ dPQ with Par-Diverges→ A merge dPQ
...   | inj₁ dP  = [] , _ ∷ [] , P , Q' , ⟹-refl , ⟹-ev Qev ⟹-refl , psoloR ¬cs pnil , inj₁ dP
...   | inj₂ dQ' = [] , _ ∷ [] , P , Q' , ⟹-refl , ⟹-ev Qev ⟹-refl , psoloR ¬cs pnil , inj₂ dQ'
Par-ov-reach-div A merge P P' Q Q' ¬cs Pev Qev (⟹-τ step rest) divW
  with brBoth-τ-elim A merge P Q P' Q' step
... | inj₁ refl with Par-reach-div A merge P' Q rest divW
...   | sP , sQ , P* , Q* , rP , rQ , inter , dd =
        _ ∷ sP , sQ , P* , Q* , ⟹-ev Pev rP , rQ , psoloL ¬cs inter , dd
Par-ov-reach-div A merge P P' Q Q' ¬cs Pev Qev (⟹-τ step rest) divW | inj₂ refl
  with Par-reach-div A merge P Q' rest divW
...   | sP , sQ , P* , Q* , rP , rQ , inter , dd =
        sP , _ ∷ sQ , P* , Q* , rP , ⟹-ev Qev rQ , psoloR ¬cs inter , dd
Par-ov-reach-div A merge P P' Q Q' ¬cs Pev Qev (⟹-ev (sVis refl ()) _) divW
Par-ov-reach-div A merge P P' Q Q' ¬cs Pev Qev (⟹-ev (sRet ()) _) divW

-- the top-level elimination on IsDivergence: the divergence sits at SOME prefix `pre`
-- of the trace s (divergences are extension-closed), decomposed via Par-reach-div.
Par-div-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
               {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {s : List (Event√ R)}
             → divergences (Par A merge P Q) s
             → Σ[ pre ∈ List (Event√ R) ] ParDivOut A merge P Q pre
Par-div-elim A merge {P = P} {Q = Q} d =
  _ , Par-reach-div A merge P Q (d .IsDivergence.reach) (d .IsDivergence.divwit)

-------------------------------------------------------------------------------------
-- DIVERGENCE INTRODUCTION (intro): re-interleave a divergence of one operand (at a
-- de-interleaved sub-trace) with the other operand's trace, per a ParInter witness,
-- into a divergence of Par P Q.  The inverse of Par-div-elim; mirrors Par-trace-intro
-- but carries the operand divergence instead of a terminal.
-------------------------------------------------------------------------------------

-- record-level prepends: a single τ / single cs-event / solo (possibly via overlap)
-- step in front of a Par divergence.
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

-- a solo outside-`A` event reaches the next Par state by a MULTI-step run (it may pass
-- through the both-offer overlap + a commit τ), so we prepend the whole Par-soloL/R
-- run in front of the inner divergence's reach.
div-soloL-prepend : (A : EventSet) (merge : Mg R₁ R₂ R)
                    (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                    {X : Set ℓ} {e : E X} {a : X} {P₁ : PTree E (ExtI E) R₁}
                    {s : List (Event√ R)}
                  → ¬ A .mem (X , e) a
                  → P ─[ ev (evl (evLabel X e a)) ]─► P₁
                  → divergences (Par A merge P₁ Q) s
                  → divergences (Par A merge P Q) (evl (evLabel X e a) ∷ s)
div-soloL-prepend A merge P Q ¬cs Pev d = record
  { prefix = _ ∷ d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split  = cong (_ ∷_) (d .IsDivergence.split) ; witness = d .IsDivergence.witness
  ; reach  = Par-soloL-reach A merge P Q ¬cs Pev (d .IsDivergence.reach)
  ; divwit = d .IsDivergence.divwit }

div-soloR-prepend : (A : EventSet) (merge : Mg R₁ R₂ R)
                    (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                    {X : Set ℓ} {e : E X} {a : X} {Q₁ : PTree E (ExtI E) R₂}
                    {s : List (Event√ R)}
                  → ¬ A .mem (X , e) a
                  → Q ─[ ev (evl (evLabel X e a)) ]─► Q₁
                  → divergences (Par A merge P Q₁) s
                  → divergences (Par A merge P Q) (evl (evLabel X e a) ∷ s)
div-soloR-prepend A merge P Q ¬cs Qev d = record
  { prefix = _ ∷ d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split  = cong (_ ∷_) (d .IsDivergence.split) ; witness = d .IsDivergence.witness
  ; reach  = Par-soloR-reach A merge P Q ¬cs Qev (d .IsDivergence.reach)
  ; divwit = d .IsDivergence.divwit }

Par-div-intro : (A : EventSet) (merge : Mg R₁ R₂ R)
                (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                {P* : PTree E (ExtI E) R₁} {Q* : PTree E (ExtI E) R₂}
                {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
              → P ⟹⟨ sP ⟩ P* → Q ⟹⟨ sQ ⟩ Q* → ParInter A merge sP sQ s
              → Diverges P* ⊎ Diverges Q*
              → divergences (Par A merge P Q) s
-- drain P's τ's
Par-div-intro A merge P Q (⟹-τ Pτ restP) Qbs PI dd =
  div-τ-prepend (Par-τ-L A merge P Q Pτ)
                (Par-div-intro A merge _ Q restP Qbs PI dd)
-- drain Q's τ's
Par-div-intro A merge P Q Pbs (⟹-τ Qτ restQ) PI dd =
  div-τ-prepend (Par-τ-R A merge P Q Qτ)
                (Par-div-intro A merge P _ Pbs restQ PI dd)
-- base: both operands settled — lift the operand divergence into the composite
Par-div-intro A merge P Q ⟹-refl ⟹-refl pnil (inj₁ dP) =
  empty-div (Par-Diverges-L A merge Q dP)
Par-div-intro A merge P Q ⟹-refl ⟹-refl pnil (inj₂ dQ) =
  empty-div (Par-Diverges-R A merge P dQ)
-- a shared (in `A`) event: both operands fire it together
Par-div-intro A merge P Q (⟹-ev Pev restP) (⟹-ev Qev restQ) (psync csat PI) dd =
  div-ev-prepend (Par-sync A merge P Q csat Pev Qev)
                 (Par-div-intro A merge _ _ restP restQ PI dd)
-- a solo (outside `A`) event on the left
Par-div-intro A merge P Q (⟹-ev Pev restP) Qbs (psoloL ¬cs PI) dd =
  div-soloL-prepend A merge P Q ¬cs Pev
                    (Par-div-intro A merge _ Q restP Qbs PI dd)
-- a solo (outside `A`) event on the right
Par-div-intro A merge P Q Pbs (⟹-ev Qev restQ) (psoloR ¬cs PI) dd =
  div-soloR-prepend A merge P Q ¬cs Qev
                    (Par-div-intro A merge P _ Pbs restQ PI dd)
-- joint √: both operands terminate, the composite goes to deadlock — which converges,
-- so the post-√ operand cannot diverge.
Par-div-intro A merge P Q (⟹-ev (sRet _) ⟹-refl) (⟹-ev (sRet _) restQ) p√ (inj₁ dP) =
  ⊥-elim (deadlock-converges dP)
Par-div-intro A merge P Q (⟹-ev (sRet _) (⟹-τ step _)) (⟹-ev (sRet _) restQ) p√ (inj₁ dP) =
  ⊥-elim (deadlock-no-τ step)
Par-div-intro A merge P Q (⟹-ev (sRet _) restP) (⟹-ev (sRet _) ⟹-refl) p√ (inj₂ dQ) =
  ⊥-elim (deadlock-converges dQ)
Par-div-intro A merge P Q (⟹-ev (sRet _) restP) (⟹-ev (sRet _) (⟹-τ step _)) p√ (inj₂ dQ) =
  ⊥-elim (deadlock-no-τ step)
