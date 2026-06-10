{-# OPTIONS --guardedness #-}
module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_States where

open import Level using (lift) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Function using (case_of_)

open import Interaction_Trees
open ITree
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS

import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP            as M
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_Deadlock   as D

-- `loop0-tail-step` import-cycle note.
--   `loop0-tail-step` lives in module `Tr` of `…_SystemP_Traces.agda`.  That
--   module imports the Deadlock module (`open D.Pf m`) but NOT this States
--   module, so the dependency chain States → Traces → Deadlock is acyclic and
--   we may open Traces here, reusing `loop0-tail-step` rather than relocating it.
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_Traces     as T

module St (m : ℕ) where
  open M.Sys m
  open D.Pf  m   -- generic loop0 / Prefix / □ machinery + fork defs; reuse, don't redefine
  open T.Tr  m   -- exposes loop0-tail-step (fires the head event of a loop0 residual)

  -- Operator / iterate / law definitions at the DP event decidability (⟶₀, >>=,
  -- loop0, Prefix-cont, bind-cont-vis, iter-bind-*, …).  `open D.Pf`/`open T.Tr`
  -- bring the project-specific lemmas into scope but NOT these library names
  -- (their own `open …` of the parametrised modules is not `public`), so we
  -- re-open them here exactly as those modules do.
  import CSP.Definitions.Operators {E = DP} as OpsD
  open OpsD DP-AnyTypes-≟
  import CSP.Definitions.Iterate {E = DP} as IterD
  open IterD DP-AnyTypes-≟
  import CSP.Laws.Bind {E = DP} as BindL
  open BindL DP-AnyTypes-≟ using (bind-force-vis)
  import CSP.Laws.Iterate {E = DP} as IterL
  open IterL DP-AnyTypes-≟ using (iter-bind-force-vis; iter-bind-cont-vis-just)

  -- General philosopher body (covers asymmetric first/second), matching the model's PHIL.
  PbodyG : (first second : Phil → Fork) → Phil → ITree DP (ExtI DP) (⊤ {lzero})
  PbodyG f s i = picks i (f i) ⟶₀ picks i (s i) ⟶₀ putsdown i (s i) ⟶₀ putsdown i (f i) ⟶₀ Skip

  Psuf1 : (f s : Phil → Fork) → Phil → ITree DP (ExtI DP) (⊤ {lzero})
  Psuf1 f s i = picks i (s i) ⟶₀ putsdown i (s i) ⟶₀ putsdown i (f i) ⟶₀ Skip
  Psuf2 : (f s : Phil → Fork) → Phil → ITree DP (ExtI DP) (⊤ {lzero})
  Psuf2 f s i = putsdown i (s i) ⟶₀ putsdown i (f i) ⟶₀ Skip
  Psuf3 : (f s : Phil → Fork) → Phil → ITree DP (ExtI DP) (⊤ {lzero})
  Psuf3 f s i = putsdown i (f i) ⟶₀ Skip

  data PhilPos : Set where think held1 held2 down1 reloop : PhilPos

  philState : (first second : Phil → Fork) → Phil → PhilPos → ITree DP (ExtI DP) ⊥
  philState f s i think  = loop0 (PbodyG f s i)
  philState f s i held1  = loop0-body-tail (PbodyG f s i) (Psuf1 f s i)
  philState f s i held2  = loop0-body-tail (PbodyG f s i) (Psuf2 f s i)
  philState f s i down1  = loop0-body-tail (PbodyG f s i) (Psuf3 f s i)
  philState f s i reloop = loop0-body-tail (PbodyG f s i) Skip

  -- The model's PHIL IS philState … think (definitional check).
  _ : ∀ {f s} i → PHIL f s i ≡ philState f s i think
  _ = λ i → refl

  -------------------------------------------------------------------------------------
  -- Philosopher force lemmas (each vis-position is vis-headed).

  pfb-think : (f s : Phil → Fork) (i : Phil)
            → (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥))
  pfb-think f s i = loop0-fb (PbodyG f s i) (Prefix-cont (picks i (f i)) (λ _ → Psuf1 f s i))

  philState-force-think : ∀ {f s} i
    → (philState f s i think) .force ≡ vis (pfb-think f s i)
  philState-force-think {f} {s} i = loop0-force (PbodyG f s i) refl

  -- held1 : after the first pick; body offer is the prefix `picks i (s i)`.
  pfb-held1 : (f s : Phil → Fork) (i : Phil)
            → (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥))
  pfb-held1 f s i =
    iter-bind-cont-vis (loopStep0 (PbodyG f s i))
      (bind-cont-vis loop-k (Prefix-cont (picks i (s i)) (λ _ → Psuf2 f s i)))

  philState-force-held1 : ∀ {f s} i
    → (philState f s i held1) .force ≡ vis (pfb-held1 f s i)
  philState-force-held1 {f} {s} i =
    iter-bind-force-vis (Psuf1 f s i >>= loop-k) (loopStep0 (PbodyG f s i))
      (bind-force-vis (Psuf1 f s i) loop-k refl)

  -- held2 : after the second pick; body offer is the prefix `putsdown i (s i)`.
  pfb-held2 : (f s : Phil → Fork) (i : Phil)
            → (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥))
  pfb-held2 f s i =
    iter-bind-cont-vis (loopStep0 (PbodyG f s i))
      (bind-cont-vis loop-k (Prefix-cont (putsdown i (s i)) (λ _ → Psuf3 f s i)))

  philState-force-held2 : ∀ {f s} i
    → (philState f s i held2) .force ≡ vis (pfb-held2 f s i)
  philState-force-held2 {f} {s} i =
    iter-bind-force-vis (Psuf2 f s i >>= loop-k) (loopStep0 (PbodyG f s i))
      (bind-force-vis (Psuf2 f s i) loop-k refl)

  -- down1 : after the first putdown; body offer is the prefix `putsdown i (f i)`.
  pfb-down1 : (f s : Phil → Fork) (i : Phil)
            → (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥))
  pfb-down1 f s i =
    iter-bind-cont-vis (loopStep0 (PbodyG f s i))
      (bind-cont-vis loop-k (Prefix-cont (putsdown i (f i)) (λ _ → Skip)))

  philState-force-down1 : ∀ {f s} i
    → (philState f s i down1) .force ≡ vis (pfb-down1 f s i)
  philState-force-down1 {f} {s} i =
    iter-bind-force-vis (Psuf3 f s i >>= loop-k) (loopStep0 (PbodyG f s i))
      (bind-force-vis (Psuf3 f s i) loop-k refl)

  -------------------------------------------------------------------------------------
  -- reloop force = sil (loop-back to think).

  philState-force-reloop : ∀ {f s} i
    → (philState f s i reloop) .force ≡ sil (philState f s i think)
  philState-force-reloop i = refl

  -------------------------------------------------------------------------------------
  -- Philosopher offer-forward lemmas (think fires its event → held1; refuses others).

  phil-think-fires : ∀ {f s} i
    → pfb-think f s i (pAt i (f i)) tt ≡ just (philState f s i held1)
  phil-think-fires {f}{s} i =
    loop0-offer-just (PbodyG f s i) (Prefix-cont (picks i (f i)) (λ _ → Psuf1 f s i))
      (prefix-picks-offer i (f i) (λ _ → Psuf1 f s i))

  phil-think-refuses-picks : ∀ {f s} i i′ f′ → ¬ ((i ≡ i′) × (f i ≡ f′))
    → pfb-think f s i (pAt i′ f′) tt ≡ nothing
  phil-think-refuses-picks {f}{s} i i′ f′ ¬eq =
    loop0-offer-nothing {at = pAt i′ f′} {a = tt}
      (PbodyG f s i) (Prefix-cont (picks i (f i)) (λ _ → Psuf1 f s i))
      (prefix-picks-refuse i (f i) i′ f′ (λ _ → Psuf1 f s i) ¬eq)

  phil-think-refuses-pd : ∀ {f s} i i′ f′
    → pfb-think f s i (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing
  phil-think-refuses-pd {f}{s} i i′ f′ =
    loop0-offer-nothing {at = ⊤ {lzero} , putsdown i′ f′} {a = tt}
      (PbodyG f s i) (Prefix-cont (picks i (f i)) (λ _ → Psuf1 f s i))
      (prefix-picks-refuse-pd i (f i) i′ f′ (λ _ → Psuf1 f s i))

  -------------------------------------------------------------------------------------
  -- Philosopher step lemmas (each position's outgoing transition).

  -- think ─picks i (f i)─► held1
  phil-step-think : ∀ {f s} i
    → philState f s i think
        ─[ ev (evl (evLabel _ (picks i (f i)) tt)) ]─► philState f s i held1
  phil-step-think {f}{s} i =
    loop0-body-step (PbodyG f s i) refl (prefix-picks-offer i (f i) (λ _ → Psuf1 f s i))

  -- held1 ─picks i (s i)─► held2
  phil-step-held1 : ∀ {f s} i
    → philState f s i held1
        ─[ ev (evl (evLabel _ (picks i (s i)) tt)) ]─► philState f s i held2
  phil-step-held1 {f}{s} i = loop0-tail-step (PbodyG f s i) (picks i (s i)) tt (Psuf2 f s i)

  -- held2 ─putsdown i (s i)─► down1
  phil-step-held2 : ∀ {f s} i
    → philState f s i held2
        ─[ ev (evl (evLabel _ (putsdown i (s i)) tt)) ]─► philState f s i down1
  phil-step-held2 {f}{s} i = loop0-tail-step (PbodyG f s i) (putsdown i (s i)) tt (Psuf3 f s i)

  -- down1 ─putsdown i (f i)─► reloop
  phil-step-down1 : ∀ {f s} i
    → philState f s i down1
        ─[ ev (evl (evLabel _ (putsdown i (f i)) tt)) ]─► philState f s i reloop
  phil-step-down1 {f}{s} i = loop0-tail-step (PbodyG f s i) (putsdown i (f i)) tt Skip

  -- reloop ─τ─► think (loop-back)
  phil-step-reloop : ∀ {f s} i → philState f s i reloop ─[ τ ]─► philState f s i think
  phil-step-reloop {f}{s} i = sSil (philState-force-reloop {f}{s} i)

  -------------------------------------------------------------------------------------
  -- Task 3: Philosopher reachability closure.
  -------------------------------------------------------------------------------------

  -- A `putsdown i f` prefix refuses a *different* `putsdown i′ f′` (indices differ).
  -- Completes the generic `prefix-*-refuse` family of the Deadlock module
  -- (`prefix-picks-refuse{,-pd}`, `prefix-putsdown-refuse-pk`); kept local here to
  -- avoid editing that module for a single downstream-only helper.
  prefix-putsdown-refuse-pd :
    ∀ {ℓr} {R : Set ℓr} (i f i′ f′ : Fork) (P : ⊤ {lzero} → ITree DP (ExtI DP) R)
    → ¬ ((i ≡ i′) × (f ≡ f′))
    → Prefix-cont (putsdown i f) P (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing
  prefix-putsdown-refuse-pd i f i′ f′ P ¬eq
    with DP-AnyTypes-≟ (⊤ {lzero} , putsdown i f) (⊤ {lzero} , putsdown i′ f′)
  ... | yes refl = ⊥-elim (¬eq (refl , refl))
  ... | no  _    = refl

  -------------------------------------------------------------------------------------
  -- Fire / refuse facts for the residual positions (mirroring the `think` family).

  -- held1 (head `picks i (s i)`)
  phil-held1-fires : ∀ {f s} i
    → pfb-held1 f s i (pAt i (s i)) tt ≡ just (philState f s i held2)
  phil-held1-fires {f}{s} i =
    loop0-offer-just (PbodyG f s i) (Prefix-cont (picks i (s i)) (λ _ → Psuf2 f s i))
      (prefix-picks-offer i (s i) (λ _ → Psuf2 f s i))

  phil-held1-refuses-picks : ∀ {f s} i i′ f′ → ¬ ((i ≡ i′) × (s i ≡ f′))
    → pfb-held1 f s i (pAt i′ f′) tt ≡ nothing
  phil-held1-refuses-picks {f}{s} i i′ f′ ¬eq =
    loop0-offer-nothing {at = pAt i′ f′} {a = tt}
      (PbodyG f s i) (Prefix-cont (picks i (s i)) (λ _ → Psuf2 f s i))
      (prefix-picks-refuse i (s i) i′ f′ (λ _ → Psuf2 f s i) ¬eq)

  phil-held1-refuses-pd : ∀ {f s} i i′ f′
    → pfb-held1 f s i (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing
  phil-held1-refuses-pd {f}{s} i i′ f′ =
    loop0-offer-nothing {at = ⊤ {lzero} , putsdown i′ f′} {a = tt}
      (PbodyG f s i) (Prefix-cont (picks i (s i)) (λ _ → Psuf2 f s i))
      (prefix-picks-refuse-pd i (s i) i′ f′ (λ _ → Psuf2 f s i))

  -- held2 (head `putsdown i (s i)`)
  phil-held2-fires : ∀ {f s} i
    → pfb-held2 f s i (⊤ {lzero} , putsdown i (s i)) tt ≡ just (philState f s i down1)
  phil-held2-fires {f}{s} i =
    loop0-offer-just (PbodyG f s i) (Prefix-cont (putsdown i (s i)) (λ _ → Psuf3 f s i))
      (Prefix-cont-just (putsdown i (s i)) (λ _ → Psuf3 f s i) tt)

  phil-held2-refuses-pk : ∀ {f s} i i′ f′
    → pfb-held2 f s i (pAt i′ f′) tt ≡ nothing
  phil-held2-refuses-pk {f}{s} i i′ f′ =
    loop0-offer-nothing {at = pAt i′ f′} {a = tt}
      (PbodyG f s i) (Prefix-cont (putsdown i (s i)) (λ _ → Psuf3 f s i))
      (prefix-putsdown-refuse-pk i (s i) i′ f′ (λ _ → Psuf3 f s i))

  phil-held2-refuses-pd : ∀ {f s} i i′ f′ → ¬ ((i ≡ i′) × (s i ≡ f′))
    → pfb-held2 f s i (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing
  phil-held2-refuses-pd {f}{s} i i′ f′ ¬eq =
    loop0-offer-nothing {at = ⊤ {lzero} , putsdown i′ f′} {a = tt}
      (PbodyG f s i) (Prefix-cont (putsdown i (s i)) (λ _ → Psuf3 f s i))
      (prefix-putsdown-refuse-pd i (s i) i′ f′ (λ _ → Psuf3 f s i) ¬eq)

  -- down1 (head `putsdown i (f i)`)
  phil-down1-fires : ∀ {f s} i
    → pfb-down1 f s i (⊤ {lzero} , putsdown i (f i)) tt ≡ just (philState f s i reloop)
  phil-down1-fires {f}{s} i =
    loop0-offer-just (PbodyG f s i) (Prefix-cont (putsdown i (f i)) (λ _ → Skip))
      (Prefix-cont-just (putsdown i (f i)) (λ _ → Skip) tt)

  phil-down1-refuses-pk : ∀ {f s} i i′ f′
    → pfb-down1 f s i (pAt i′ f′) tt ≡ nothing
  phil-down1-refuses-pk {f}{s} i i′ f′ =
    loop0-offer-nothing {at = pAt i′ f′} {a = tt}
      (PbodyG f s i) (Prefix-cont (putsdown i (f i)) (λ _ → Skip))
      (prefix-putsdown-refuse-pk i (f i) i′ f′ (λ _ → Skip))

  phil-down1-refuses-pd : ∀ {f s} i i′ f′ → ¬ ((i ≡ i′) × (f i ≡ f′))
    → pfb-down1 f s i (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing
  phil-down1-refuses-pd {f}{s} i i′ f′ ¬eq =
    loop0-offer-nothing {at = ⊤ {lzero} , putsdown i′ f′} {a = tt}
      (PbodyG f s i) (Prefix-cont (putsdown i (f i)) (λ _ → Skip))
      (prefix-putsdown-refuse-pd i (f i) i′ f′ (λ _ → Skip) ¬eq)

  -------------------------------------------------------------------------------------
  -- Offer-classifier helpers.  Given that an offer function (`pfb-pos`) yields `just t″`
  -- on the *concrete* event `(picks/putsdown i′ f′)`, decide whether that event is the
  -- position's head event (then `t″` is the next state) or not (then the offer is
  -- `nothing` and the hypothesis is absurd).  These take `gja` as a clean argument, so
  -- the internal `DP-AnyTypes-≟` decision is not entangled with the caller's goal.

  -- A `picks`-headed position (think, held1) at offered `picks i′ f′`.  Decide whether
  -- the event is the head (`pAt i hd ≡ pAt i′ f′`): if so `subst` the fire equation onto
  -- the offered event and bridge with `gja`; else the refuse equation makes `gja` absurd.
  -- This is purely propositional (no `with` over the offer's buried decision).
  phil-pk-det :
    ∀ {f s} i (hd : Fork) {t″}
    → (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
    → (res : PhilPos)
    → (fires  : fb (pAt i hd) tt ≡ just (philState f s i res))
    → (refuse : ∀ i′ f′ → ¬ ((i ≡ i′) × (hd ≡ f′)) → fb (pAt i′ f′) tt ≡ nothing)
    → ∀ i′ f′ → fb (pAt i′ f′) tt ≡ just t″
    → t″ ≡ philState f s i res
  phil-pk-det {f}{s} i hd fb res fires refuse i′ f′ gja
    with i Fin.≟ i′ | hd Fin.≟ f′
  ... | yes refl | yes refl = sym (just-injective (trans (sym fires) gja))
  ... | no ¬i | _ = case trans (sym (refuse i′ f′ (λ { (e , _) → ¬i e }))) gja of λ ()
  ... | _ | no ¬h = case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬h e }))) gja of λ ()

  -- A `putsdown`-headed position (held2, down1) at offered `putsdown i′ f′`.
  phil-pd-det :
    ∀ {f s} i (hd : Fork) {t″}
    → (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
    → (res : PhilPos)
    → (fires  : fb (⊤ {lzero} , putsdown i hd) tt ≡ just (philState f s i res))
    → (refuse : ∀ i′ f′ → ¬ ((i ≡ i′) × (hd ≡ f′)) → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing)
    → ∀ i′ f′ → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ just t″
    → t″ ≡ philState f s i res
  phil-pd-det {f}{s} i hd fb res fires refuse i′ f′ gja
    with i Fin.≟ i′ | hd Fin.≟ f′
  ... | yes refl | yes refl = sym (just-injective (trans (sym fires) gja))
  ... | no ¬i | _ = case trans (sym (refuse i′ f′ (λ { (e , _) → ¬i e }))) gja of λ ()
  ... | _ | no ¬h = case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬h e }))) gja of λ ()

  -------------------------------------------------------------------------------------
  -- THE CRUX: every state big-step-reachable from a philosopher position is again a
  -- philosopher position (for the SAME f, s, i).  Induction on the big-step derivation.

  phil-reach-closed : ∀ {f s} i (pos : PhilPos) {sₜ t′}
    → philState f s i pos ═⟨ sₜ ⟩═► t′
    → Σ[ pos′ ∈ PhilPos ] (t′ ≡ philState f s i pos′)

  -- bNil : nothing happens.
  phil-reach-closed i pos bNil = pos , refl

  -- bTau : a τ-step.  Only `reloop` is sil-headed; all vis positions reject τ.
  phil-reach-closed {f}{s} i think (bTau τstep _) =
    ⊥-elim (τ-from-force-vis-impossible (philState-force-think {f}{s} i) τstep)
  phil-reach-closed {f}{s} i held1 (bTau τstep _) =
    ⊥-elim (τ-from-force-vis-impossible (philState-force-held1 {f}{s} i) τstep)
  phil-reach-closed {f}{s} i held2 (bTau τstep _) =
    ⊥-elim (τ-from-force-vis-impossible (philState-force-held2 {f}{s} i) τstep)
  phil-reach-closed {f}{s} i down1 (bTau τstep _) =
    ⊥-elim (τ-from-force-vis-impossible (philState-force-down1 {f}{s} i) τstep)
  phil-reach-closed {f}{s} i reloop (bTau (sSil {t = t″} eqf) rest)
    with sil-injective (trans (sym (philState-force-reloop {f}{s} i)) eqf)
  ... | refl = phil-reach-closed i think rest
  phil-reach-closed {f}{s} i reloop (bTau (sNdbr eqf _) _) =
    case trans (sym eqf) (philState-force-reloop {f}{s} i) of λ ()
  phil-reach-closed {f}{s} i reloop (bTau (sMixSlide eqf) _) =
    case trans (sym eqf) (philState-force-reloop {f}{s} i) of λ ()

  -- bStep : a visible ev-step.  `reloop` is sil-headed (no ev); each vis position
  -- fires exactly its own head event and refuses everything else.
  phil-reach-closed {f}{s} i reloop (bStep (sVis eqf _) _) =
    case trans (sym eqf) (philState-force-reloop {f}{s} i) of λ ()
  phil-reach-closed {f}{s} i reloop (bStep (sMixVis eqf _) _) =
    case trans (sym eqf) (philState-force-reloop {f}{s} i) of λ ()

  phil-reach-closed {f}{s} i think
    (bStep (sVis {at = _ , picks i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (philState-force-think {f}{s} i)) =
        phil-reach-closed i held1
          (subst (λ z → z ═⟨ _ ⟩═► _)
                 (phil-pk-det {f}{s} i (f i) (pfb-think f s i) held1
                        (phil-think-fires {f}{s} i)
                        (λ i″ f″ ¬eq → phil-think-refuses-picks {f}{s} i i″ f″ ¬eq)
                        i′ f′ gja) rest)
  phil-reach-closed {f}{s} i think
    (bStep (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (philState-force-think {f}{s} i)) =
        case trans (sym (phil-think-refuses-pd {f}{s} i i′ f′)) gja of λ ()
  phil-reach-closed {f}{s} i think (bStep (sMixVis eqf _) _) =
    case trans (sym eqf) (philState-force-think {f}{s} i) of λ ()

  phil-reach-closed {f}{s} i held1
    (bStep (sVis {at = _ , picks i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (philState-force-held1 {f}{s} i)) =
        phil-reach-closed i held2
          (subst (λ z → z ═⟨ _ ⟩═► _)
                 (phil-pk-det {f}{s} i (s i) (pfb-held1 f s i) held2
                        (phil-held1-fires {f}{s} i)
                        (λ i″ f″ ¬eq → phil-held1-refuses-picks {f}{s} i i″ f″ ¬eq)
                        i′ f′ gja) rest)
  phil-reach-closed {f}{s} i held1
    (bStep (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (philState-force-held1 {f}{s} i)) =
        case trans (sym (phil-held1-refuses-pd {f}{s} i i′ f′)) gja of λ ()
  phil-reach-closed {f}{s} i held1 (bStep (sMixVis eqf _) _) =
    case trans (sym eqf) (philState-force-held1 {f}{s} i) of λ ()

  phil-reach-closed {f}{s} i held2
    (bStep (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (philState-force-held2 {f}{s} i)) =
        phil-reach-closed i down1
          (subst (λ z → z ═⟨ _ ⟩═► _)
                 (phil-pd-det {f}{s} i (s i) (pfb-held2 f s i) down1
                        (phil-held2-fires {f}{s} i)
                        (λ i″ f″ ¬eq → phil-held2-refuses-pd {f}{s} i i″ f″ ¬eq)
                        i′ f′ gja) rest)
  phil-reach-closed {f}{s} i held2
    (bStep (sVis {at = _ , picks i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (philState-force-held2 {f}{s} i)) =
        case trans (sym (phil-held2-refuses-pk {f}{s} i i′ f′)) gja of λ ()
  phil-reach-closed {f}{s} i held2 (bStep (sMixVis eqf _) _) =
    case trans (sym eqf) (philState-force-held2 {f}{s} i) of λ ()

  phil-reach-closed {f}{s} i down1
    (bStep (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (philState-force-down1 {f}{s} i)) =
        phil-reach-closed i reloop
          (subst (λ z → z ═⟨ _ ⟩═► _)
                 (phil-pd-det {f}{s} i (f i) (pfb-down1 f s i) reloop
                        (phil-down1-fires {f}{s} i)
                        (λ i″ f″ ¬eq → phil-down1-refuses-pd {f}{s} i i″ f″ ¬eq)
                        i′ f′ gja) rest)
  phil-reach-closed {f}{s} i down1
    (bStep (sVis {at = _ , picks i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (philState-force-down1 {f}{s} i)) =
        case trans (sym (phil-down1-refuses-pk {f}{s} i i′ f′)) gja of λ ()
  phil-reach-closed {f}{s} i down1 (bStep (sMixVis eqf _) _) =
    case trans (sym eqf) (philState-force-down1 {f}{s} i) of λ ()

  -- Corollary: PHIL f s i ≡ philState f s i think (definitionally).
  PHIL-states : ∀ {f s} i {sₜ t′}
    → PHIL f s i ═⟨ sₜ ⟩═► t′
    → Σ[ pos ∈ PhilPos ] (t′ ≡ philState f s i pos)
  PHIL-states i big = phil-reach-closed i think big

  -------------------------------------------------------------------------------------
  -- Task 4: Fork positions + force/offer/step lemmas
  -------------------------------------------------------------------------------------

  -- Own-branch residual (after picks j j) is Pf's `forkRes j`; neighbour residual is new.
  forkResNbr : Fork → ITree DP (ExtI DP) ⊥
  forkResNbr j = loop0-body-tail (Fbody j) (putsdown (j ⊖1) j ⟶₀ Skip)

  data ForkPos : Set where free heldOwn heldNbr reloop : ForkPos

  forkState : Fork → ForkPos → ITree DP (ExtI DP) ⊥
  forkState j free    = loop0 (Fbody j)
  forkState j heldOwn = forkRes j
  forkState j heldNbr = forkResNbr j
  forkState j reloop  = loop0-body-tail (Fbody j) Skip

  _ : ∀ j → FORK j ≡ forkState j free
  _ = λ j → refl

  -------------------------------------------------------------------------------------
  -- Fork force lemmas.

  forkState-force-free : ∀ j → (forkState j free) .force ≡ vis (loop0-fb (Fbody j) (FORK-fb j))
  forkState-force-free j = FORK-force j

  forkState-force-heldOwn : ∀ j → (forkState j heldOwn) .force ≡ vis (forkRes-fb j)
  forkState-force-heldOwn j = forkRes-force j

  -- Neighbour residual offer function (head prefix `putsdown (j ⊖1) j`, cont `λ _ → Skip`).
  forkResNbr-fb : ∀ j → (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥))
  forkResNbr-fb j = iter-bind-cont-vis (loopStep0 (Fbody j))
                      (bind-cont-vis loop-k (Prefix-cont (putsdown (j ⊖1) j) (λ _ → Skip)))

  forkResNbr-force : ∀ j → (forkState j heldNbr) .force ≡ vis (forkResNbr-fb j)
  forkResNbr-force j =
    iter-bind-force-vis ((putsdown (j ⊖1) j ⟶₀ Skip) >>= loop-k) (loopStep0 (Fbody j))
      (bind-force-vis (putsdown (j ⊖1) j ⟶₀ Skip) loop-k refl)

  forkState-force-reloop : ∀ j → (forkState j reloop) .force ≡ sil (forkState j free)
  forkState-force-reloop j = refl

  -------------------------------------------------------------------------------------
  -- Body-level (⊤-valued) offer facts for `Fbody j`'s two `□`-branches, feeding both
  -- `loop0-offer-just` (→ ⊥-level `loop0-fb` fact) and `loop0-body-step`.
  -- (`□-offer-R` (right branch fires, left refuses) is already provided by `T.Tr`.)

  -- own branch fires `picks j j` (left fires, right refuses since j⊖1 ≢ j).
  FORK-body-fires-own : ∀ j
    → FORK-fb j (pAt j j) tt ≡ just (putsdown j j ⟶₀ Skip)
  FORK-body-fires-own j =
    □-offer-L (Prefix-cont (picks j j)      (λ _ → putsdown j j      ⟶₀ Skip))
              (Prefix-cont (picks (j ⊖1) j) (λ _ → putsdown (j ⊖1) j ⟶₀ Skip))
              tt
              (prefix-picks-offer j j (λ _ → putsdown j j ⟶₀ Skip))
              (prefix-picks-refuse (j ⊖1) j j j (λ _ → putsdown (j ⊖1) j ⟶₀ Skip)
                (λ { (e , _) → ⊖1-≢ j e }))

  -- neighbour branch fires `picks (j⊖1) j` (right fires, left refuses since j⊖1 ≢ j).
  FORK-body-fires-nbr : ∀ j
    → FORK-fb j (pAt (j ⊖1) j) tt ≡ just (putsdown (j ⊖1) j ⟶₀ Skip)
  FORK-body-fires-nbr j =
    □-offer-R (pAt (j ⊖1) j)
              (Prefix-cont (picks j j)      (λ _ → putsdown j j      ⟶₀ Skip))
              (Prefix-cont (picks (j ⊖1) j) (λ _ → putsdown (j ⊖1) j ⟶₀ Skip))
              tt
              (prefix-picks-refuse j j (j ⊖1) j (λ _ → putsdown j j ⟶₀ Skip)
                (λ { (e , _) → ⊖1-≢ j (sym e) }))
              (prefix-picks-offer (j ⊖1) j (λ _ → putsdown (j ⊖1) j ⟶₀ Skip))

  -- free fires picks (j⊖1) j to heldNbr via the RIGHT □-branch (left refuses since j⊖1 ≢ j).
  -- (Named `′` to avoid clashing with `T.Tr`'s concrete-fork `FORK-fires-nbr`.)
  FORK-fires-nbr′ : ∀ j
    → loop0-fb (Fbody j) (FORK-fb j) (pAt (j ⊖1) j) tt ≡ just (forkResNbr j)
  FORK-fires-nbr′ j =
    loop0-offer-just (Fbody j) (FORK-fb j) (FORK-body-fires-nbr j)

  -------------------------------------------------------------------------------------
  -- Fork step lemmas (each position's outgoing transition).

  fork-step-own : ∀ j
    → forkState j free ─[ ev (evl (evLabel _ (picks j j) tt)) ]─► forkState j heldOwn
  fork-step-own j = loop0-body-step (Fbody j) (FORK-body-force j) (FORK-body-fires-own j)

  fork-step-nbr : ∀ j
    → forkState j free ─[ ev (evl (evLabel _ (picks (j ⊖1) j) tt)) ]─► forkState j heldNbr
  fork-step-nbr j = loop0-body-step (Fbody j) (FORK-body-force j) (FORK-body-fires-nbr j)

  fork-step-heldOwn : ∀ j
    → forkState j heldOwn ─[ ev (evl (evLabel _ (putsdown j j) tt)) ]─► forkState j reloop
  fork-step-heldOwn j = loop0-tail-step (Fbody j) (putsdown j j) tt Skip

  fork-step-heldNbr : ∀ j
    → forkState j heldNbr ─[ ev (evl (evLabel _ (putsdown (j ⊖1) j) tt)) ]─► forkState j reloop
  fork-step-heldNbr j = loop0-tail-step (Fbody j) (putsdown (j ⊖1) j) tt Skip

  fork-step-reloop : ∀ j → forkState j reloop ─[ τ ]─► forkState j free
  fork-step-reloop j = sSil (forkState-force-reloop j)

  -------------------------------------------------------------------------------------
  -- Task 5: Fork reachability closure (THE CRUX, branching `free`).
  -------------------------------------------------------------------------------------

  -- Fire facts re-exposed at the States naming (own/nbr fire `free`'s two events).
  -- `FORK-fires j` (own, from D.Pf) gives `just (forkRes j)` ≡ `just (forkState j heldOwn)`;
  -- `FORK-fires-nbr′ j` (above) gives `just (forkResNbr j)` ≡ `just (forkState j heldNbr)`.

  -- heldOwn (single head `putsdown j j`) fires → reloop.
  fork-heldOwn-fires : ∀ j
    → forkRes-fb j (⊤ {lzero} , putsdown j j) tt ≡ just (forkState j reloop)
  fork-heldOwn-fires j =
    loop0-offer-just (Fbody j) (Prefix-cont (putsdown j j) (λ _ → Skip))
      (Prefix-cont-just (putsdown j j) (λ _ → Skip) tt)

  -- heldNbr (single head `putsdown (j ⊖1) j`) fires → reloop.
  fork-heldNbr-fires : ∀ j
    → forkResNbr-fb j (⊤ {lzero} , putsdown (j ⊖1) j) tt ≡ just (forkState j reloop)
  fork-heldNbr-fires j =
    loop0-offer-just (Fbody j) (Prefix-cont (putsdown (j ⊖1) j) (λ _ → Skip))
      (Prefix-cont-just (putsdown (j ⊖1) j) (λ _ → Skip) tt)

  -------------------------------------------------------------------------------------
  -- Refuse facts.

  -- free refuses a `picks i′ f′` that is NEITHER own (j,j) NOR neighbour (j⊖1,j).
  -- Both `□`-branches refuse via `prefix-picks-refuse`.
  fork-free-refuses-pk : ∀ j i′ f′
    → ¬ ((j ≡ i′) × (j ≡ f′)) → ¬ (((j ⊖1) ≡ i′) × (j ≡ f′))
    → loop0-fb (Fbody j) (FORK-fb j) (pAt i′ f′) tt ≡ nothing
  fork-free-refuses-pk j i′ f′ ¬own ¬nbr =
    loop0-offer-nothing {at = pAt i′ f′} {a = tt} (Fbody j) (FORK-fb j)
      (□-offer-refuse (Prefix-cont (picks j j)      (λ _ → putsdown j j      ⟶₀ Skip))
                      (Prefix-cont (picks (j ⊖1) j) (λ _ → putsdown (j ⊖1) j ⟶₀ Skip))
                      tt
                      (prefix-picks-refuse j j i′ f′ (λ _ → putsdown j j ⟶₀ Skip) ¬own)
                      (prefix-picks-refuse (j ⊖1) j i′ f′ (λ _ → putsdown (j ⊖1) j ⟶₀ Skip) ¬nbr))

  -- free refuses every `putsdown` (both `□`-branches are picks-headed).
  fork-free-refuses-pd : ∀ j i′ f′
    → loop0-fb (Fbody j) (FORK-fb j) (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing
  fork-free-refuses-pd j i′ f′ =
    loop0-offer-nothing {at = ⊤ {lzero} , putsdown i′ f′} {a = tt} (Fbody j) (FORK-fb j)
      (□-offer-refuse {at = ⊤ {lzero} , putsdown i′ f′}
                      (Prefix-cont (picks j j)      (λ _ → putsdown j j      ⟶₀ Skip))
                      (Prefix-cont (picks (j ⊖1) j) (λ _ → putsdown (j ⊖1) j ⟶₀ Skip))
                      tt
                      (prefix-picks-refuse-pd j j i′ f′ (λ _ → putsdown j j ⟶₀ Skip))
                      (prefix-picks-refuse-pd (j ⊖1) j i′ f′ (λ _ → putsdown (j ⊖1) j ⟶₀ Skip)))

  -- heldOwn refuses every `picks` (reuse D.Pf's `forkRes-refuses-pk`) and every OTHER
  -- `putsdown` (head is `putsdown j j`).
  fork-heldOwn-refuses-pk : ∀ j i′ f′ → forkRes-fb j (pAt i′ f′) tt ≡ nothing
  fork-heldOwn-refuses-pk j i′ f′ = forkRes-refuses-pk j i′ f′

  fork-heldOwn-refuses-pd : ∀ j i′ f′ → ¬ ((j ≡ i′) × (j ≡ f′))
    → forkRes-fb j (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing
  fork-heldOwn-refuses-pd j i′ f′ ¬eq =
    loop0-offer-nothing {at = ⊤ {lzero} , putsdown i′ f′} {a = tt} (Fbody j)
      (Prefix-cont (putsdown j j) (λ _ → Skip))
      (prefix-putsdown-refuse-pd j j i′ f′ (λ _ → Skip) ¬eq)

  -- heldNbr refuses every `picks` and every OTHER `putsdown` (head is `putsdown (j⊖1) j`).
  fork-heldNbr-refuses-pk : ∀ j i′ f′ → forkResNbr-fb j (pAt i′ f′) tt ≡ nothing
  fork-heldNbr-refuses-pk j i′ f′ =
    loop0-offer-nothing {at = pAt i′ f′} {a = tt} (Fbody j)
      (Prefix-cont (putsdown (j ⊖1) j) (λ _ → Skip))
      (prefix-putsdown-refuse-pk (j ⊖1) j i′ f′ (λ _ → Skip))

  fork-heldNbr-refuses-pd : ∀ j i′ f′ → ¬ (((j ⊖1) ≡ i′) × (j ≡ f′))
    → forkResNbr-fb j (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing
  fork-heldNbr-refuses-pd j i′ f′ ¬eq =
    loop0-offer-nothing {at = ⊤ {lzero} , putsdown i′ f′} {a = tt} (Fbody j)
      (Prefix-cont (putsdown (j ⊖1) j) (λ _ → Skip))
      (prefix-putsdown-refuse-pd (j ⊖1) j i′ f′ (λ _ → Skip) ¬eq)

  -------------------------------------------------------------------------------------
  -- Offer-classifiers (mirror Task 3's `phil-pk-det`/`phil-pd-det`, keeping the offer
  -- function `fb` abstract so the buried `DP-AnyTypes-≟`/`mergeVis` does not block).

  -- THE BRANCHING CASE: `free`'s offer fires at TWO `picks` events.  Given the offer is
  -- `just t″` at a concrete `picks i′ f′`, decide a 3-way split: own (j,j) → heldOwn,
  -- neighbour (j⊖1,j) → heldNbr, otherwise refused (absurd).  The two fire-events are
  -- distinct because `j ⊖1 ≢ j` (`⊖1-≢`), so the own/nbr cases never overlap.
  fork-free-pk-det :
    ∀ j {t″}
    → (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
    → (fires-own : fb (pAt j j) tt ≡ just (forkState j heldOwn))
    → (fires-nbr : fb (pAt (j ⊖1) j) tt ≡ just (forkState j heldNbr))
    → (refuse : ∀ i′ f′ → ¬ ((j ≡ i′) × (j ≡ f′)) → ¬ (((j ⊖1) ≡ i′) × (j ≡ f′))
              → fb (pAt i′ f′) tt ≡ nothing)
    → ∀ i′ f′ → fb (pAt i′ f′) tt ≡ just t″
    → Σ[ pos′ ∈ ForkPos ] (t″ ≡ forkState j pos′)
  fork-free-pk-det j fb fires-own fires-nbr refuse i′ f′ gja
    with j Fin.≟ i′ | (j ⊖1) Fin.≟ i′ | j Fin.≟ f′
  ... | yes refl | _        | yes refl =
        heldOwn , sym (just-injective (trans (sym fires-own) gja))
  ... | no ¬o    | yes refl | yes refl =
        heldNbr , sym (just-injective (trans (sym fires-nbr) gja))
  ... | no ¬o    | no ¬nb   | yes refl =
        case trans (sym (refuse i′ f′ (λ { (e , _) → ¬o e }) (λ { (e , _) → ¬nb e }))) gja
          of λ ()
  ... | yes refl | _        | no ¬f =
        case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬f e }) (λ { (_ , e) → ¬f e }))) gja
          of λ ()
  ... | no ¬o    | yes refl | no ¬f =
        case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬f e }) (λ { (_ , e) → ¬f e }))) gja
          of λ ()
  ... | no ¬o    | no ¬nb   | no ¬f =
        case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬f e }) (λ { (_ , e) → ¬f e }))) gja
          of λ ()

  -- A single-head `putsdown`-position classifier (heldOwn / heldNbr → reloop).
  fork-pd-det :
    ∀ j (hi hf : Fork) {t″}
    → (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
    → (fires  : fb (⊤ {lzero} , putsdown hi hf) tt ≡ just (forkState j reloop))
    → (refuse : ∀ i′ f′ → ¬ ((hi ≡ i′) × (hf ≡ f′)) → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing)
    → ∀ i′ f′ → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ just t″
    → t″ ≡ forkState j reloop
  fork-pd-det j hi hf fb fires refuse i′ f′ gja
    with hi Fin.≟ i′ | hf Fin.≟ f′
  ... | yes refl | yes refl = sym (just-injective (trans (sym fires) gja))
  ... | no ¬i | _ = case trans (sym (refuse i′ f′ (λ { (e , _) → ¬i e }))) gja of λ ()
  ... | _ | no ¬h = case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬h e }))) gja of λ ()

  -------------------------------------------------------------------------------------
  -- THE CRUX: every state big-step-reachable from a fork position is again a fork
  -- position (same j).  Induction on the big-step derivation (mirrors Task 3).

  fork-reach-closed : ∀ j (pos : ForkPos) {sₜ t′}
    → forkState j pos ═⟨ sₜ ⟩═► t′
    → Σ[ pos′ ∈ ForkPos ] (t′ ≡ forkState j pos′)

  -- bNil : nothing happens.
  fork-reach-closed j pos bNil = pos , refl

  -- bTau : a τ-step.  Only `reloop` is sil-headed; all vis positions reject τ.
  fork-reach-closed j free (bTau τstep _) =
    ⊥-elim (τ-from-force-vis-impossible (forkState-force-free j) τstep)
  fork-reach-closed j heldOwn (bTau τstep _) =
    ⊥-elim (τ-from-force-vis-impossible (forkState-force-heldOwn j) τstep)
  fork-reach-closed j heldNbr (bTau τstep _) =
    ⊥-elim (τ-from-force-vis-impossible (forkResNbr-force j) τstep)
  fork-reach-closed j reloop (bTau (sSil {t = t″} eqf) rest)
    with sil-injective (trans (sym (forkState-force-reloop j)) eqf)
  ... | refl = fork-reach-closed j free rest
  fork-reach-closed j reloop (bTau (sNdbr eqf _) _) =
    case trans (sym eqf) (forkState-force-reloop j) of λ ()
  fork-reach-closed j reloop (bTau (sMixSlide eqf) _) =
    case trans (sym eqf) (forkState-force-reloop j) of λ ()

  -- bStep : a visible ev-step.  `reloop` is sil-headed (no ev); each vis position
  -- fires exactly its own head event(s) and refuses everything else.
  fork-reach-closed j reloop (bStep (sVis eqf _) _) =
    case trans (sym eqf) (forkState-force-reloop j) of λ ()
  fork-reach-closed j reloop (bStep (sMixVis eqf _) _) =
    case trans (sym eqf) (forkState-force-reloop j) of λ ()

  -- free : branches on `picks i′ f′` (own → heldOwn, nbr → heldNbr); refuses putsdown.
  fork-reach-closed j free
    (bStep (sVis {at = _ , picks i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (forkState-force-free j))
    with fork-free-pk-det j (loop0-fb (Fbody j) (FORK-fb j))
           (FORK-fires j) (FORK-fires-nbr′ j)
           (λ i″ f″ ¬o ¬nb → fork-free-refuses-pk j i″ f″ ¬o ¬nb)
           i′ f′ gja
  ... | pos′ , eq = fork-reach-closed j pos′ (subst (λ z → z ═⟨ _ ⟩═► _) eq rest)
  fork-reach-closed j free
    (bStep (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (forkState-force-free j)) =
        case trans (sym (fork-free-refuses-pd j i′ f′)) gja of λ ()
  fork-reach-closed j free (bStep (sMixVis eqf _) _) =
    case trans (sym eqf) (forkState-force-free j) of λ ()

  -- heldOwn : single head `putsdown j j` → reloop; refuses picks and other putsdown.
  fork-reach-closed j heldOwn
    (bStep (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (forkState-force-heldOwn j)) =
        fork-reach-closed j reloop
          (subst (λ z → z ═⟨ _ ⟩═► _)
                 (fork-pd-det j j j (forkRes-fb j)
                        (fork-heldOwn-fires j)
                        (λ i″ f″ ¬eq → fork-heldOwn-refuses-pd j i″ f″ ¬eq)
                        i′ f′ gja) rest)
  fork-reach-closed j heldOwn
    (bStep (sVis {at = _ , picks i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (forkState-force-heldOwn j)) =
        case trans (sym (fork-heldOwn-refuses-pk j i′ f′)) gja of λ ()
  fork-reach-closed j heldOwn (bStep (sMixVis eqf _) _) =
    case trans (sym eqf) (forkState-force-heldOwn j) of λ ()

  -- heldNbr : single head `putsdown (j⊖1) j` → reloop; refuses picks and other putsdown.
  fork-reach-closed j heldNbr
    (bStep (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (forkResNbr-force j)) =
        fork-reach-closed j reloop
          (subst (λ z → z ═⟨ _ ⟩═► _)
                 (fork-pd-det j (j ⊖1) j (forkResNbr-fb j)
                        (fork-heldNbr-fires j)
                        (λ i″ f″ ¬eq → fork-heldNbr-refuses-pd j i″ f″ ¬eq)
                        i′ f′ gja) rest)
  fork-reach-closed j heldNbr
    (bStep (sVis {at = _ , picks i′ f′} {a = tt} eqf gja) rest)
    rewrite vis-inj (trans (sym eqf) (forkResNbr-force j)) =
        case trans (sym (fork-heldNbr-refuses-pk j i′ f′)) gja of λ ()
  fork-reach-closed j heldNbr (bStep (sMixVis eqf _) _) =
    case trans (sym eqf) (forkResNbr-force j) of λ ()

  -- Corollary: FORK j ≡ forkState j free (definitionally).
  FORK-states : ∀ j {sₜ t′}
    → FORK j ═⟨ sₜ ⟩═► t′ → Σ[ pos ∈ ForkPos ] (t′ ≡ forkState j pos)
  FORK-states j big = fork-reach-closed j free big

-------------------------------------------------------------------------------------
-- Task 6: m = 0 (n = 2) sanity check.
--
-- Cheap elaboration checks at the smallest instance (`open St 0`, so `n = 2`,
-- `Phil = Fork = Fin 2`).  The force lemmas show the start positions are vis-headed
-- (`philState … think`, `forkState … free`), and the reachability corollaries return
-- the start position on the empty (`bNil`) trace — `PHIL/FORK-states … bNil` computes
-- to `(think , refl)` / `(free , refl)` definitionally.
-------------------------------------------------------------------------------------

module Sanity where
  open M.Sys 0  -- symFirst / symSecond / Phil / Fork at n = 2
  open St 0

  -- Start positions elaborate and are vis-headed.
  _ : (philState symFirst symSecond Fin.zero think) .force ≡ vis (pfb-think symFirst symSecond Fin.zero)
  _ = philState-force-think {symFirst} {symSecond} Fin.zero

  _ : Σ[ fb ∈ _ ] ((forkState Fin.zero free) .force ≡ vis fb)
  _ = _ , forkState-force-free Fin.zero

  -- Closure corollaries return the start position on the empty trace.
  _ : PHIL-states {symFirst} {symSecond} Fin.zero bNil ≡ (think , refl)
  _ = refl

  _ : FORK-states Fin.zero bNil ≡ (free , refl)
  _ = refl
