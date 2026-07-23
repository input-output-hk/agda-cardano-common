{-# OPTIONS --guardedness --safe #-}

------------------------------------------------------------------------
-- Priority Laws: the Layer-2 executable priority operator `Pri`
-- (`CSP.Priority.Base`) is a STRONG-bisimulation congruence:
--
--   P ∼ Q  ⇒  Pri O P fbP ∼ Pri O Q fbQ            (for any FinBr certificates)
--
-- Strategy (direct, one-pass, no transitivity on corecursive residuals):
-- a step of `Pri O P fbP` is INVERTED to the underlying PLAIN P-step plus its
-- firing conditions (dominance / maximality / stability), the plain step is
-- TRANSPORTED through `P ∼ Q`, the firing conditions are RE-ESTABLISHED on Q
-- via the agreement lemmas (`∼→stable`, `dom-agree`, maximality is node-free),
-- and `Pri O Q fbQ` RE-FIRES the matching step.  The residual is a BARE
-- corecursive `cong-∼ (cgr …)` (never under `subst`/`trans`/`sbisim-sym`), so
-- guardedness holds exactly as in `CSP.Priority.Tau`'s `agree-τfree-∼`.
--
-- `--safe`, 0 postulates, nothing from `Classical`/`dne`, no `NON_TERMINATING`.
-- All Pri inversion/firing lemmas are reused from `CSP.Priority.Adequacy`.
------------------------------------------------------------------------

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong₂)

open import Process_Trees
open PTree

module CSP.Priority.Laws.Cong {ℓ ℓe} {E : Set ℓ → Set ℓe} where

open import Semantics.PriOrder {ℓ} {ℓe} {E}
open import Semantics.LTS      {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Bisim    {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import CSP.Priority.Base          {ℓ} {ℓe} {E}
open import CSP.Priority.Adequacy  {ℓ} {ℓe} {E}

------------------------------------------------------------------------
-- Order-independent stability helpers (re-derived here; the analogues in
-- `Semantics.DRImpliesFD` live in a non-`--safe` module because of an
-- unrelated postulate there).
------------------------------------------------------------------------

-- `nothing ≡ just x` is absurd
nothing≢just : ∀ {ℓa} {A : Set ℓa} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

-- a stable state's force cannot be `sil`
stable-not-sil : ∀ {ℓr} {R : Set ℓr} {t u : PTree E (ExtI E) R}
               → isStable t → PTree.force t ≡ sil u → ⊥
stable-not-sil {t = t} st eq with PTree.force t | st | eq
... | ret _     | _       | ()
... | sil _     | lift ()  | _
... | react _ _ | _       | ()

-- a stable state's force cannot be `ret` (ret is never stable)
stable-not-ret : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R} {r : R}
               → isStable t → PTree.force t ≡ ret r → ⊥
stable-not-ret {t = t} st eq with PTree.force t | st | eq
... | ret _     | lift ()  | _
... | sil _     | _        | ()
... | react _ _ | _        | ()

-- a stable state's τ-branch continuation is everywhere `nothing`
stable-react-τc : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
                    {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                → isStable t → PTree.force t ≡ react v τc
                → ∀ i a → τc i a ≡ nothing
stable-react-τc {t = t} st eq with PTree.force t | st | eq
... | ret _     | _    | ()
... | sil _     | _    | ()
... | react _ _ | stf  | refl = stf

-- hence a stable state performs no τ-step at all
stable-no-τ : ∀ {ℓr} {R : Set ℓr} {t u : PTree E (ExtI E) R}
            → isStable t → t ─[ τ ]─► u → ⊥
stable-no-τ {t = t} st (sSil eq) = stable-not-sil {t = t} st eq
stable-no-τ {t = t} st (sTau {i = i} {a = a} eq br) =
  nothing≢just (trans (sym (stable-react-τc {t = t} st eq i a)) br)

-- stability transports along strong bisimulation
∼→stable : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
         → P ∼ Q → isStable P → isStable Q
∼→stable {P = P} {Q = Q} p∼ stP with PTree.force Q in eqfQ
-- Q rets ⇒ Q has a √-step ⇒ so does P (via ∼) ⇒ P is not stable: absurd
... | ret r with p∼ .Sbisim.bwd .SSimF.on-ev (sRet eqfQ)
...   | _ , sRet eqfP , _ = ⊥-elim (stable-not-ret {t = P} stP eqfP)
-- Q sils ⇒ Q has a τ-step ⇒ so does P ⇒ P is not stable: absurd
∼→stable {P = P} {Q = Q} p∼ stP | sil c with p∼ .Sbisim.bwd .SSimF.on-tau (sSil eqfQ)
...   | _ , pstep , _ = ⊥-elim (stable-no-τ {t = P} stP pstep)
-- Q reacts ⇒ show every τ-branch is `nothing` (an enabled one would give P a τ)
∼→stable {P = P} {Q = Q} p∼ stP | react vQ τcQ = allNothing
  where
    allNothing : ∀ i a → τcQ i a ≡ nothing
    allNothing i a with τcQ i a in teq
    ... | nothing = refl
    ... | just t′ with p∼ .Sbisim.bwd .SSimF.on-tau (sTau eqfQ teq)
    ...   | _ , pstep , _ = ⊥-elim (stable-no-τ {t = P} stP pstep)

-- pointwise agreement of the visible-offer support along `∼`
is-just-agree : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
                  {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcP τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
              → P ∼ Q → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
              → ∀ at a → is-just (vP at a) ≡ is-just (vQ at a)
is-just-agree {vP = vP} {vQ = vQ} p∼ eqfP eqfQ at a with vP at a in vpeq | vQ at a in vqeq
... | nothing  | nothing  = refl
... | just _   | just _   = refl
-- P offers here, Q does not: transport P's offer to a Q-offer, contradiction
... | just tP′ | nothing  with p∼ .Sbisim.fwd .SSimF.on-ev (sVis eqfP vpeq)
...   | tQ′ , qstep , _ with offers→just eqfQ (tQ′ , qstep)
...     | _ , vqjust = ⊥-elim (nothing≢just (trans (sym vqeq) vqjust))
-- Q offers here, P does not: symmetric
is-just-agree {vP = vP} {vQ = vQ} p∼ eqfP eqfQ at a | nothing | just tQ′
      with p∼ .Sbisim.bwd .SSimF.on-ev (sVis eqfQ vqeq)
...   | tP′ , pstep , _ with offers→just eqfP (tP′ , pstep)
...     | _ , vpjust = ⊥-elim (nothing≢just (trans (sym vpeq) vpjust))

------------------------------------------------------------------------
-- Order-dependent development.
------------------------------------------------------------------------

module _ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo) where

  -- the `dominated?` scan is invariant along `∼` (pointwise via `is-just-agree`)
  dom-agree : {P Q : PTree E (ExtI E) R}
                {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {τcP τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
            → P ∼ Q → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
            → ∀ e → dominated? O vP e ≡ dominated? O vQ e
  dom-agree {vP = vP} {vQ = vQ} p∼ eqfP eqfQ e = go (PriOrder.above O e)
    where
      go : (bs : List Ev)
         → foldr (λ b acc → is-just (vP (b .at) (b .val)) ∨ acc) false bs
         ≡ foldr (λ b acc → is-just (vQ (b .at) (b .val)) ∨ acc) false bs
      go []       = refl
      go (b ∷ bs) = cong₂ _∨_ (is-just-agree p∼ eqfP eqfQ (b .at) (b .val)) (go bs)

  -- an ≤-maximal event is undominated in Q as well (maximality + `dom-agree`)
  max→domQ : {P Q : PTree E (ExtI E) R}
               {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {τcP τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
               {e : Ev}
           → P ∼ Q → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
           → isMax? O e ≡ true → dominated? O vQ e ≡ false
  max→domQ {vP = vP} p∼ eqfP eqfQ mx =
    trans (sym (dom-agree p∼ eqfP eqfQ _)) (Max→dom-false O {v = vP} (isMax?→Max {R = R} O mx))

  -- fire a single τ-step of `Pri O W fbW` from a plain τ-step of `W`
  fireτ : {W : PTree E (ExtI E) R} (fbW : FinBr W) {tW′ : PTree E (ExtI E) R}
        → W ─[ τ ]─► tW′
        → Σ[ fbW′ ∈ FinBr tW′ ] (Pri O W fbW ─[ τ ]─► Pri O tW′ fbW′)
  fireτ fbW (sSil eqfW) =
    let (eqf , peq) = fPri-sil O {fb = fbW} eqfW
    in  FinBr.next fbW (sSil eqf) , sSil peq
  fireτ {W = W} fbW (sTau {τc = τc} {i = i} {a = a} eqfW brW) with fPri-react O {fb = fbW} eqfW
  ... | inj₁ (stW , eqf , peq) =
        ⊥-elim (nothing≢just (trans (sym (isStable-react O {t = W} eqf stW i a)) brW))
  ... | inj₂ (¬stW , eqf , peq) =
        let (eia , tfire) = priTauAt-fires O eqf {fb = fbW} (τc i a) refl brW
        in  FinBr.next fbW (sTau eqf eia) , sTau peq tfire

  -- fire a single visible step of `Pri O W fbW` from a plain visible step of `W`;
  -- the caller supplies the firing conditions for whichever polarity `W` has.
  fireEv : {W : PTree E (ExtI E) R} (fbW : FinBr W)
             {vW : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τcW : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
             {at : AnyTypes E} {a : proj₁ at} {tW′ : PTree E (ExtI E) R}
         → PTree.force W ≡ react vW τcW → vW at a ≡ just tW′
         → (isStable W → dominated? O vW (at ∙ a) ≡ false)
         → (¬ isStable W → isMax? O (at ∙ a) ≡ true)
         → Σ[ fbW′ ∈ FinBr tW′ ]
             (Pri O W fbW ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► Pri O tW′ fbW′)
  fireEv fbW {vW = vW} {at = at} {a = a} eqfW evaW domf maxf with fPri-react O {fb = fbW} eqfW
  -- stable ⇒ priVis fires because no dominator is offered
  ... | inj₁ (stW , eqf , peq) =
        let (eva , vfire) = priVisAt-fires O eqf {fb = fbW}
                              (dominated? O vW (at ∙ a)) refl (vW at a) refl (domf stW) evaW
        in  FinBr.next fbW (sVis eqf eva) , sVis peq vfire
  -- unstable ⇒ priMax fires because the event is ≤-maximal
  ... | inj₂ (¬stW , eqf , peq) =
        let (eva , mfire) = priMaxAt-fires O eqf {fb = fbW}
                              (isMax? O (at ∙ a)) refl (vW at a) refl (maxf ¬stW) evaW
        in  FinBr.next fbW (sVis eqf eva) , sVis peq mfire

  ------------------------------------------------------------------------
  -- The congruence relation + guarded coinduction (mirrors `agree-τfree-∼`).
  ------------------------------------------------------------------------

  -- both sides are the priorities of two strongly-bisimilar processes
  data CongR : PTree E (ExtI E) R → PTree E (ExtI E) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    cgr : {P Q : PTree E (ExtI E) R} (p∼ : P ∼ Q) (fbP : FinBr P) (fbQ : FinBr Q)
        → CongR (Pri O P fbP) (Pri O Q fbQ)

  -- forward declarations (the corecursion lives in `afwd`'s BODY, cf. ssim-trans)
  cong-∼ : {A B : PTree E (ExtI E) R} → CongR A B → A ∼ B
  afwd   : {P Q : PTree E (ExtI E) R} → P ∼ Q → (fbP : FinBr P) (fbQ : FinBr Q)
         → SSimF (Sbisim R) (Pri O P fbP) (Pri O Q fbQ)

  -- `.bwd` is `.fwd` of the symmetric instance: `afwd (sbisim-sym p∼) fbQ fbP`
  cong-∼ (cgr p∼ fbP fbQ) .Sbisim.fwd = afwd p∼ fbP fbQ
  cong-∼ (cgr p∼ fbP fbQ) .Sbisim.bwd = afwd (sbisim-sym p∼) fbQ fbP

  -- visible-step simulation of `Pri O P fbP` by `Pri O Q fbQ`
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-ev step with PTree.force P in eqfP
  -- P rets: a √-step; transport to Q's √-step, re-fire, residual deadlock∼deadlock
  ... | ret r with step
  ...   | sRet eq
          with p∼ .Sbisim.fwd .SSimF.on-ev
                 (sRet (trans eqfP (trans (sym (fPri-ret O eqfP)) eq)))
  ...     | _ , sRet eqfQ , _ = deadlock , sRet (fPri-ret O eqfQ) , sbisim-refl deadlock
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-ev step | ret r | sVis eq _ =
        case trans (sym (fPri-ret O eqfP)) eq of λ ()
  -- P sils: no visible step (its `Pri` head is `sil`)
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-ev step | sil c with step
  ...   | sRet eq   = case trans (sym (proj₂ (fPri-sil O {fb = fbP} eqfP))) eq of λ ()
  ...   | sVis eq _ = case trans (sym (proj₂ (fPri-sil O {fb = fbP} eqfP))) eq of λ ()
  -- P reacts: split on P's stability polarity
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-ev step | react vP τcP
        with fPri-react O {fb = fbP} eqfP | step
  -- STABLE P ⇒ priVis fired (a non-maximal offer allowed by the empty dominator set)
  ...   | inj₁ (stP , eqfP′ , peq) | sRet eq = case trans (sym peq) eq of λ ()
  ...   | inj₁ (stP , eqfP′ , peq) | sVis {at = at} {a = a} eq br
          with priVisAt-just O eqfP′ {fb = fbP} (dominated? O vP (at ∙ a)) refl (vP at a) refl
                 (subst (λ w → w at a ≡ just _)
                        (sym (proj₁ (react-injective (trans (sym peq) eq)))) br)
  ...     | tP′ , dmf , eva , refl
            with p∼ .Sbisim.fwd .SSimF.on-ev (sVis eqfP′ eva)
  ...       | tQ′ , qstep , tP∼tQ with ev-inv qstep
  ...         | vQ , τcQ , eqfQ , evaQ
                with fireEv fbQ eqfQ evaQ
                       (λ _ → trans (sym (dom-agree p∼ eqfP′ eqfQ (at ∙ a))) dmf)
                       (λ ¬stQ → ⊥-elim (¬stQ (∼→stable p∼ stP)))
  ...           | fbQ′ , qfire =
                  Pri O tQ′ fbQ′ , qfire
                    , cong-∼ (cgr tP∼tQ (FinBr.next fbP (sVis eqfP′ eva)) fbQ′)
  -- UNSTABLE P ⇒ priMax fired (the offer is ≤-maximal, node-independent)
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-ev step | react vP τcP
        | inj₂ (¬stP , eqfP′ , peq) | sRet eq = case trans (sym peq) eq of λ ()
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-ev step | react vP τcP
        | inj₂ (¬stP , eqfP′ , peq) | sVis {at = at} {a = a} eq br
          with priMaxAt-just O eqfP′ {fb = fbP} (isMax? O (at ∙ a)) refl (vP at a) refl
                 (subst (λ w → w at a ≡ just _)
                        (sym (proj₁ (react-injective (trans (sym peq) eq)))) br)
  ...     | tP′ , mxtrue , eva , refl
            with p∼ .Sbisim.fwd .SSimF.on-ev (sVis eqfP′ eva)
  ...       | tQ′ , qstep , tP∼tQ with ev-inv qstep
  ...         | vQ , τcQ , eqfQ , evaQ
                with fireEv fbQ eqfQ evaQ
                       (λ _ → max→domQ p∼ eqfP′ eqfQ mxtrue)
                       (λ _ → mxtrue)
  ...           | fbQ′ , qfire =
                  Pri O tQ′ fbQ′ , qfire
                    , cong-∼ (cgr tP∼tQ (FinBr.next fbP (sVis eqfP′ eva)) fbQ′)

  -- τ-step simulation of `Pri O P fbP` by `Pri O Q fbQ`
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-tau step with PTree.force P in eqfP
  -- P rets: no τ-step
  ... | ret r with step
  ...   | sSil eq   = case trans (sym (fPri-ret O eqfP)) eq of λ ()
  ...   | sTau eq _ = case trans (sym (fPri-ret O eqfP)) eq of λ ()
  -- P sils: a τ-step to `c`; transport to a Q τ-step, re-fire
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-tau step | sil c
        with fPri-sil O {fb = fbP} eqfP | step
  ...   | eqf , peq | sSil eq with sil-injective (trans (sym peq) eq)
  ...     | refl with p∼ .Sbisim.fwd .SSimF.on-tau (sSil eqf)
  ...       | tQ′ , qstep , cP∼tQ with fireτ fbQ qstep
  ...         | fbQ′ , qfire =
                Pri O tQ′ fbQ′ , qfire
                  , cong-∼ (cgr cP∼tQ (FinBr.next fbP (sSil eqf)) fbQ′)
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-tau step | sil c | eqf , peq | sTau eq _ =
        case trans (sym peq) eq of λ ()
  -- P reacts: split on stability polarity
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-tau step | react vP τcP
        with fPri-react O {fb = fbP} eqfP | step
  -- STABLE P ⇒ empty τ-branch ⇒ no τ-step
  ...   | inj₁ (stP , eqfP′ , peq) | sSil eq = case trans (sym peq) eq of λ ()
  ...   | inj₁ (stP , eqfP′ , peq) | sTau {i = i} {a = a} eq br =
          case subst (λ w → w i a ≡ just _)
                 (sym (proj₂ (react-injective (trans (sym peq) eq)))) br of λ ()
  -- UNSTABLE P ⇒ priTau fired; transport to a Q τ-step, re-fire
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-tau step | react vP τcP
        | inj₂ (¬stP , eqfP′ , peq) | sSil eq = case trans (sym peq) eq of λ ()
  afwd {P} {Q} p∼ fbP fbQ .SSimF.on-tau step | react vP τcP
        | inj₂ (¬stP , eqfP′ , peq) | sTau {i = i} {a = a} eq br
          with priTauAt-just O eqfP′ {fb = fbP} (τcP i a) refl
                 (subst (λ w → w i a ≡ just _)
                        (sym (proj₂ (react-injective (trans (sym peq) eq)))) br)
  ...     | tP′ , eia , refl
            with p∼ .Sbisim.fwd .SSimF.on-tau (sTau eqfP′ eia)
  ...       | tQ′ , qstep , tP∼tQ with fireτ fbQ qstep
  ...         | fbQ′ , qfire =
                Pri O tQ′ fbQ′ , qfire
                  , cong-∼ (cgr tP∼tQ (FinBr.next fbP (sTau eqfP′ eia)) fbQ′)

------------------------------------------------------------------------
-- MAIN: `Pri` is a strong-bisimulation congruence.
------------------------------------------------------------------------

-- `P ∼ Q` ⇒ `Pri O P fbP ∼ Pri O Q fbQ` for any stability certificates
pri-cong : ∀ {ℓo ℓr} {R : Set ℓr} {O : PriOrder ℓo} {P Q : PTree E (ExtI E) R}
         → P ∼ Q → (fbP : FinBr P) (fbQ : FinBr Q) → Pri O P fbP ∼ Pri O Q fbQ
pri-cong {O = O} p∼ fbP fbQ = cong-∼ O (cgr p∼ fbP fbQ)
