{-# OPTIONS --guardedness #-}

-- FROZEN COMPONENTS: swapping out an interleaved operand that can never move.
--
-- THE SITUATION.  A composite of the shape
--
--     (P ⦀ Rest) ∥⇘ A ⇙ D
--
-- where `P` is a component whose EVERY visible offer lies inside the synchronisation
-- set `A`, and `D` is a partner that never offers any of those events.  Then `P` can
-- never take a step at all: it has no τ (it is stable), its visible offers all need an
-- `A`-rendezvous with `D`, and `D` refuses to supply one.  `P` is therefore INVARIANT
-- along every run of the composite, and it contributes nothing to the composite's
-- traces, offers or refusals.
--
-- WHAT IS PROVED.  `frozen-swap-⊑F` says such a `P` may be replaced by ANY other
-- component `Q` that is frozen in the same sense, as a stable-failures refinement:
--
--     ((Q ⦀ Rest) ∥⇘ A ⇙ D)  ⊑F  ((P ⦀ Rest) ∥⇘ A ⇙ D)
--
-- Taking `Q := Stop` (`Frozen-Stop`) DELETES the frozen component: the reduced
-- composite carries a closed constant where the original carried a stateful process,
-- so a downstream refinement proof never has to track its state.  The hypotheses are
-- SYMMETRIC in `P` and `Q`, so the reverse refinement is the same lemma applied the
-- other way round (`frozen-swap-⊑F-both`) — hence `≈F`-style interchangeability.
--
-- WHY THIS SHAPE AND NOT ANOTHER.
--   * NOT a bare `Offers`/`Refuses` fact.  Those describe ONE state; a refinement proof
--     would still have to carry the frozen component through every state of its
--     simulation.  The point of the lemma is to remove it from the term.
--   * NOT a one-level `⊑F` fact about `P ⦀ Rest` alone.  That is FALSE: at the `⦀`
--     level (synchronisation set `∅ES`) the frozen component's offers are unblocked and
--     fire solo.  The blocking happens only at the `∥⇘ A ⇙ D` level, so the statement
--     must span BOTH operator levels.  This is why it cannot be obtained from the
--     existing `⦀-mono-⊑F` congruence.
--   * `⊑F` (not `⊑FD`) so that no divergence obligation on the composite is incurred:
--     the witness is an `FSimF` (`Semantics.FailureSim`), which has no `div→` field.
-- Everything ABOVE the `∥⇘ A ⇙` level is then handled by the existing unconditional
-- monotonicity laws (`Par-mono-⊑F`, `⦀-mono-⊑F`, `Hide-mono-⊑F`), so one instance of
-- this lemma lifts to an arbitrarily deep surrounding context.
--
-- REACHABILITY.  The partner hypothesis must hold at every state `D` can reach, not
-- merely initially, so `Partner` is COINDUCTIVE (`next` closes it under every step).
-- The frozen component needs no such closure: it never moves, so its initial state is
-- its only state, and `Frozen` is an ordinary record.
--
-- POSTULATES.  This module depends on `CSP.Laws.FD.ParallelRefusals`, whose `offer-LEM`
-- is the pre-existing (`dne`-certifiable) postulate already incurred by
-- `Par-mono-⊑FD`.  It adds none of its own, and contains no hole and no pragma.

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Function using (case_of_)

open import Process_Trees

module CSP.Laws.FD.FrozenComponent {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet

open import Semantics.LTS        {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
  using (WSimF; _═[_]═►_; wτ; wev; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures   {E = E} {I = ExtI E} using (_⊑F_)
open import Semantics.Refusals   {E = E} {I = ExtI E} using (Offers)
open import Semantics.Stability  {E = E} {I = ExtI E}
  using (stable-no-τ; stable-not-ret)
open import Semantics.FailureSim {E = E} {I = ExtI E} using (FSimF; fsimF→⊑F)

open import CSP.Laws.Traces.TraceLawsParallel     E-≟
  using (Mg; Par-sync; Par-soloL; Par-soloR; Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using ( ParevR; evSync; evL; evR; evBoth; ev√; Par-ev-elim
        ; ParτR; τL; τR; Par-τ-elim; Par-force-ret-inv; viewV-ev)
open import CSP.Laws.FD.ParallelRefusals E-≟
  using ( Par-offer-elim; Par-offer-sync; Par-offer-soloL; Par-offer-soloR
        ; Par-stable; Par-stable-termR; stable-no-√-offer)
open import CSP.Laws.FD.ParallelMonoFD   E-≟ using (ParNormal; Par-stable-normal)

-------------------------------------------------------------------------------------
-- §1.  The two invariants.
-------------------------------------------------------------------------------------

-- `Frozen Δ T`: the COMPONENT-side hypothesis — `T` has no enabled τ, and every
-- visible event it offers lies in the event predicate `Δ`.  No coinduction is needed:
-- under the partner hypothesis below `T` never steps, so this single state is all there
-- is.  (`Δ` is a bare predicate, not an `EventSet`: no decidability is used.)
record Frozen {ℓr} (Δ : (at : AnyTypes E) → proj₁ at → Set)
              (T : PTree E (ExtI E) (⊤ {ℓr})) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  field
    stableT : isStable T
    confine : ∀ {X : Set ℓ} {f : E X} {a : X}
            → Offers T (evl (evLabel X f a)) → Δ (X , f) a
open Frozen public

-- `Partner Δ A D`: the PARTNER-side coinductive invariant, holding at every state `D`
-- can reach.  `avoid` — `D` never offers a `Δ`-event, so the frozen component can never
-- rendezvous with it.  `inside` — every event `D` offers lies in the synchronisation set
-- `A`, so `D` never takes a solo step (which is what rules out the both-offer overlap
-- node `par-brBoth` at the outer parallel, and with it any need to relate those nodes).
record Partner {ℓr} (Δ : (at : AnyTypes E) → proj₁ at → Set) (A : EventSet)
               (D : PTree E (ExtI E) (⊤ {ℓr})) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    avoid  : ∀ {X : Set ℓ} {f : E X} {a : X}
           → Δ (X , f) a → ¬ Offers D (evl (evLabel X f a))
    inside : ∀ {X : Set ℓ} {f : E X} {a : X}
           → Offers D (evl (evLabel X f a)) → A .mem (X , f) a
    next   : ∀ {l : Label (⊤ {ℓr})} {D′ : PTree E (ExtI E) (⊤ {ℓr})}
           → D ─[ l ]─► D′ → Partner Δ A D′
open Partner public

-------------------------------------------------------------------------------------
-- §2.  Plumbing shared by every case below.
-------------------------------------------------------------------------------------

private
  -- `∅ES` contains nothing, so every event is outside it.  `∅ES .mem` is CONSTANTLY
  -- `⊥`, so stating this with event arguments would leave them undetermined at every
  -- use site (both sides reduce to `⊥ → ⊥` before the implicits are ever solved) —
  -- hence the argument-free type.
  ∉∅ES : ⊥ → ⊥
  ∉∅ES z = z

  -- a non-offer, transported to the MENU level: this is the shape `Par-soloL` /
  -- `Par-soloR` consume, and it keeps the idle operand un-forced at use sites
  no-offer→menu : ∀ {ℓr} {T : PTree E (ExtI E) (⊤ {ℓr})}
                    {X : Set ℓ} {f : E X} {a : X}
                → ¬ Offers T (evl (evLabel X f a))
                → viewV (PTree.force T) (X , f) a ≡ nothing
  no-offer→menu {T = T} {X} {f} {a} noff
    with viewV (PTree.force T) (X , f) a in veq
  ... | nothing = refl
  ... | just T′ = ⊥-elim (noff (T′ , viewV-ev {P = T} refl veq))

  -- a stable component's bundle `T ⦀ Rest` never forces to `ret` (a joint √ would need
  -- `T` at `ret`, and a `ret` state is not stable)
  bundle-not-ret : ∀ {ℓr} {T Rest : PTree E (ExtI E) (⊤ {ℓr})} {r : ⊤ {ℓr}}
                 → isStable T → PTree.force (T ⦀ Rest) ≡ ret r → ⊥
  bundle-not-ret {T = T} stT eqB =
    case Par-force-ret-inv ∅ES (λ _ _ → tt) eqB of
      λ { (_ , _ , eqT , _ , _) → stable-not-ret {t = T} stT eqT }

  -- a visible step of the bundle comes from `Rest` alone, given that the frozen
  -- component does not offer that event: the `⦀`-synchronised case is empty (`∅ES`),
  -- the two component-solo cases contradict the non-offer, and the joint-√ case
  -- contradicts stability
  bundle-ev : ∀ {ℓr} {T Rest b′ : PTree E (ExtI E) (⊤ {ℓr})}
                {X : Set ℓ} {f : E X} {a : X}
            → isStable T → ¬ Offers T (evl (evLabel X f a))
            → (T ⦀ Rest) ─[ ev (evl (evLabel X f a)) ]─► b′
            → Σ[ Rest′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ]
                ((Rest ─[ ev (evl (evLabel X f a)) ]─► Rest′) × (b′ ≡ (T ⦀ Rest′)))
  bundle-ev {T = T} {Rest = Rest} stT noff step
    with Par-ev-elim ∅ES (λ _ _ → tt) T Rest step
  ... | evSync csat _ _ = ⊥-elim csat
  ... | evL    _ stp    = ⊥-elim (noff (_ , stp))
  ... | evR    _ stp    = _ , stp , refl
  ... | evBoth _ stp _  = ⊥-elim (noff (_ , stp))

  -- likewise a τ of the bundle comes from `Rest` alone (the frozen component is stable)
  bundle-τ : ∀ {ℓr} {T Rest b′ : PTree E (ExtI E) (⊤ {ℓr})}
           → isStable T → (T ⦀ Rest) ─[ τ ]─► b′
           → Σ[ Rest′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ]
               ((Rest ─[ τ ]─► Rest′) × (b′ ≡ (T ⦀ Rest′)))
  bundle-τ {T = T} {Rest = Rest} stT step with Par-τ-elim ∅ES (λ _ _ → tt) T Rest step
  ... | τL _ stp refl = ⊥-elim (stable-no-τ stT stp)
  ... | τR _ stp refl = _ , stp , refl

  -- an OFFER of the bundle likewise routes to `Rest` (the offer-level twin of
  -- `bundle-ev`, needed for the `stab` field where no residual is available)
  bundle-offer : ∀ {ℓr} {T Rest : PTree E (ExtI E) (⊤ {ℓr})}
                   {X : Set ℓ} {f : E X} {a : X}
               → ¬ Offers T (evl (evLabel X f a))
               → Offers (T ⦀ Rest) (evl (evLabel X f a))
               → Offers Rest (evl (evLabel X f a))
  bundle-offer {T = T} {Rest = Rest} noff oB
    with Par-offer-elim ∅ES (λ _ _ → tt) T Rest oB
  ... | inj₁ (csat , _ , _) = ⊥-elim csat
  ... | inj₂ (_ , inj₁ oT)  = ⊥-elim (noff oT)
  ... | inj₂ (_ , inj₂ oR)  = oR

  -- rebuild a `Rest` step inside the bundle: the frozen component is idle at that
  -- event, and the `⦀` sync set is empty, so this is a plain solo-right step
  bundle-ev-intro : ∀ {ℓr} {T Rest Rest′ : PTree E (ExtI E) (⊤ {ℓr})}
                      {X : Set ℓ} {f : E X} {a : X}
                  → ¬ Offers T (evl (evLabel X f a))
                  → Rest ─[ ev (evl (evLabel X f a)) ]─► Rest′
                  → (T ⦀ Rest) ─[ ev (evl (evLabel X f a)) ]─► (T ⦀ Rest′)
  bundle-ev-intro {T = T} {Rest = Rest} noff stp =
    Par-soloR ∅ES (λ _ _ → tt) T Rest ∉∅ES stp (no-offer→menu {T = T} noff)

  -- a bundle whose frozen component is stable is stable exactly when `Rest` is stable
  -- or terminated — a condition that does not mention the frozen component, so it
  -- transfers verbatim across the swap
  bundle-stable-swap : ∀ {ℓr} {T U Rest : PTree E (ExtI E) (⊤ {ℓr})}
                     → isStable T → isStable U
                     → isStable (T ⦀ Rest) → isStable (U ⦀ Rest)
  bundle-stable-swap {T = T} {U = U} {Rest = Rest} stT stU stB
    with Par-stable-normal ∅ES (λ _ _ → tt) T Rest stB
  ... | inj₁ (_ , stR)            = Par-stable       ∅ES (λ _ _ → tt) U Rest stU stR
  ... | inj₂ (inj₁ (_ , eqT , _)) = ⊥-elim (stable-not-ret {t = T} stT eqT)
  ... | inj₂ (inj₂ (_ , _ , eqR)) = Par-stable-termR ∅ES (λ _ _ → tt) U Rest stU eqR

-------------------------------------------------------------------------------------
-- §3.  The simulation.  `P` is the implementation-side frozen component and `Q` the
--      specification-side one; the hypotheses are symmetric, so the roles may be
--      exchanged (see §4).
-------------------------------------------------------------------------------------

module _ {ℓr} (A : EventSet) (Δ : (at : AnyTypes E) → proj₁ at → Set)
         (Δ⊆A : ∀ {X : Set ℓ} {f : E X} {a : X} → Δ (X , f) a → A .mem (X , f) a)
         (P Q : PTree E (ExtI E) (⊤ {ℓr}))
         (fP : Frozen Δ P) (fQ : Frozen Δ Q) where

  -- the relation the simulation runs over: the two composites differ ONLY in the frozen
  -- component; `Rest` and `D` are shared, and `D` still satisfies the partner invariant
  data FRel : PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr})
            → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    frel : (Rest D : PTree E (ExtI E) (⊤ {ℓr})) → Partner Δ A D
         → FRel ((P ⦀ Rest) ∥⇘ A ⇙ D) ((Q ⦀ Rest) ∥⇘ A ⇙ D)

  private
    -- a frozen component cannot be the source of an OUTSIDE-`A` event: its offers are
    -- in `Δ ⊆ A`
    no-outside : ∀ {T : PTree E (ExtI E) (⊤ {ℓr})}
               → Frozen Δ T → ∀ {X : Set ℓ} {f : E X} {a : X}
               → ¬ A .mem (X , f) a → ¬ Offers T (evl (evLabel X f a))
    no-outside fr ¬cs off = ¬cs (Δ⊆A (fr .confine off))

    -- …nor of a SYNCHRONISED one: the partner never offers a `Δ`-event
    no-sync : ∀ {T D : PTree E (ExtI E) (⊤ {ℓr})}
            → Frozen Δ T → Partner Δ A D → ∀ {X : Set ℓ} {f : E X} {a : X}
            → Offers D (evl (evLabel X f a)) → ¬ Offers T (evl (evLabel X f a))
    no-sync fr pd oD off = pd .avoid (fr .confine off) oD

    -- composite stability transfers across the swap: by `Par-stable-normal` it reduces
    -- to conditions on `Rest` and `D` only (the frozen-component-at-`ret` branch is
    -- refuted by its stability)
    swap-stable : ∀ {Rest D : PTree E (ExtI E) (⊤ {ℓr})}
                → isStable ((P ⦀ Rest) ∥⇘ A ⇙ D) → isStable ((Q ⦀ Rest) ∥⇘ A ⇙ D)
    swap-stable {Rest} {D} st with Par-stable-normal A (λ _ _ → tt) (P ⦀ Rest) D st
    ... | inj₁ (stB , stD) =
            Par-stable A (λ _ _ → tt) (Q ⦀ Rest) D
              (bundle-stable-swap (fP .stableT) (fQ .stableT) stB) stD
    ... | inj₂ (inj₁ (_ , eqB , _)) = ⊥-elim (bundle-not-ret (fP .stableT) eqB)
    ... | inj₂ (inj₂ (stB , _ , eqD)) =
            Par-stable-termR A (λ _ _ → tt) (Q ⦀ Rest) D
              (bundle-stable-swap (fP .stableT) (fQ .stableT) stB) eqD

    -- every offer of the SPEC-side composite is an offer of the IMPL-side one: the
    -- spec's offers can only come from `Rest` (routed through the idle `Q`) or from `D`,
    -- and both are shared, so each is rebuilt on the impl side by the matching
    -- `Par-offer-sync` / `-soloL` / `-soloR` introduction.  A √-offer is impossible
    -- because the spec composite is stable.
    swap-offer : ∀ {Rest D : PTree E (ExtI E) (⊤ {ℓr})} → Partner Δ A D
               → isStable ((Q ⦀ Rest) ∥⇘ A ⇙ D)
               → ∀ (e : Event√ (⊤ {ℓr}))
               → Offers ((Q ⦀ Rest) ∥⇘ A ⇙ D) e → Offers ((P ⦀ Rest) ∥⇘ A ⇙ D) e
    swap-offer {Rest} {D} pd stC (evl (evLabel X f a)) oC
      with Par-offer-elim A (λ _ _ → tt) (Q ⦀ Rest) D oC
    ... | inj₁ (csat , oB , oD) =
            Par-offer-sync A (λ _ _ → tt) (P ⦀ Rest) D csat
              (Par-offer-soloR ∅ES (λ _ _ → tt) P Rest ∉∅ES
                (bundle-offer (no-sync fQ pd oD) oB)) oD
    ... | inj₂ (¬csat , inj₁ oB) =
            Par-offer-soloL A (λ _ _ → tt) (P ⦀ Rest) D ¬csat
              (Par-offer-soloR ∅ES (λ _ _ → tt) P Rest ∉∅ES
                (bundle-offer (no-outside fQ ¬csat) oB))
    ... | inj₂ (¬csat , inj₂ oD) = Par-offer-soloR A (λ _ _ → tt) (P ⦀ Rest) D ¬csat oD
    swap-offer {Rest} {D} pd stC (√ r) oC =
      ⊥-elim (stable-no-√-offer {t = (Q ⦀ Rest) ∥⇘ A ⇙ D} stC oC)

  -- the corecursion, split into its `WSimF` half and the record half (forward
  -- declarations rather than a `mutual` block, as elsewhere in the FSim layer)
  wsimf-frozen : ∀ {p q} → FRel p q → WSimF (FSimF (⊤ {ℓr})) p q
  fsimf-frozen : ∀ {p q} → FRel p q → FSimF (⊤ {ℓr}) p q

  -- VISIBLE steps.  Only two of the five `Par-ev-elim` cases survive: a synchronised
  -- event (the partner joins in, so the frozen component is not the source) and a
  -- left-solo event (outside `A`, so again not the frozen component).  A right-solo or
  -- both-offer step would need `D` to offer an outside-`A` event, which `Partner.inside`
  -- forbids; a joint √ would need the frozen component at `ret`.
  wsimf-frozen (frel Rest D pd) .WSimF.on-ev step
    with Par-ev-elim A (λ _ _ → tt) (P ⦀ Rest) D step
  ... | evSync csat bstep dstep
        with bundle-ev (fP .stableT) (no-sync fP pd (_ , dstep)) bstep
  ...     | Rest′ , rstep , refl =
              _
            , wev τ*-refl
                  (Par-sync A (λ _ _ → tt) (Q ⦀ Rest) D csat
                    (bundle-ev-intro (no-sync fQ pd (_ , dstep)) rstep) dstep)
                  τ*-refl
            , fsimf-frozen (frel Rest′ _ (pd .next dstep))
  wsimf-frozen (frel Rest D pd) .WSimF.on-ev step
    | evL ¬cs bstep
      with bundle-ev (fP .stableT) (no-outside fP ¬cs) bstep
  ...   | Rest′ , rstep , refl =
            _
          , wev τ*-refl
                (Par-soloL A (λ _ _ → tt) (Q ⦀ Rest) D ¬cs
                  (bundle-ev-intro (no-outside fQ ¬cs) rstep)
                  (no-offer→menu {T = D} (λ oD → ¬cs (pd .inside oD))))
                τ*-refl
          , fsimf-frozen (frel Rest′ D pd)
  wsimf-frozen (frel Rest D pd) .WSimF.on-ev step
    | evR   ¬cs dstep   = ⊥-elim (¬cs (pd .inside (_ , dstep)))
  wsimf-frozen (frel Rest D pd) .WSimF.on-ev step
    | evBoth ¬cs _ dstep = ⊥-elim (¬cs (pd .inside (_ , dstep)))
  wsimf-frozen (frel Rest D pd) .WSimF.on-ev step
    | ev√ eqB _          = ⊥-elim (bundle-not-ret (fP .stableT) eqB)

  -- τ steps.  A bundle τ is `Rest`'s (the frozen component is stable); a partner τ is
  -- replayed verbatim, carrying the partner invariant along `Partner.next`.
  wsimf-frozen (frel Rest D pd) .WSimF.on-tau step
    with Par-τ-elim A (λ _ _ → tt) (P ⦀ Rest) D step
  ... | τL _ bstep refl with bundle-τ (fP .stableT) bstep
  ...   | Rest′ , rstep , refl =
            _
          , wτ (τ*-step (Par-τ-L A (λ _ _ → tt) (Q ⦀ Rest) D
                          (Par-τ-R ∅ES (λ _ _ → tt) Q Rest rstep)) τ*-refl)
          , fsimf-frozen (frel Rest′ D pd)
  wsimf-frozen (frel Rest D pd) .WSimF.on-tau step
    | τR D′ dstep refl =
        _
      , wτ (τ*-step (Par-τ-R A (λ _ _ → tt) (Q ⦀ Rest) D dstep) τ*-refl)
      , fsimf-frozen (frel Rest D′ (pd .next dstep))

  fsimf-frozen r .FSimF.fwd = wsimf-frozen r
  -- the spec settles WHERE IT STANDS (`τ*-refl`): the swap changes neither stability
  -- nor the offer set, so no silent settling is required
  fsimf-frozen (frel Rest D pd) .FSimF.stab st =
      _ , τ*-refl , swap-stable st , swap-offer pd (swap-stable st)

  -- HEADLINE.  Swapping one frozen interleaved component for another is a stable-
  -- failures refinement, for every `Rest` and every partner satisfying the invariant.
  frozen-swap-⊑F : (Rest D : PTree E (ExtI E) (⊤ {ℓr})) → Partner Δ A D
                 → ((Q ⦀ Rest) ∥⇘ A ⇙ D) ⊑F ((P ⦀ Rest) ∥⇘ A ⇙ D)
  frozen-swap-⊑F Rest D pd = fsimF→⊑F (fsimf-frozen (frel Rest D pd))

-------------------------------------------------------------------------------------
-- §4.  `Stop` is frozen for free, so the swap DELETES the component.
-------------------------------------------------------------------------------------

-- `Stop` offers nothing and has no τ, so it is frozen for EVERY event predicate
Frozen-Stop : ∀ {ℓr} (Δ : (at : AnyTypes E) → proj₁ at → Set) → Frozen Δ (Stop {ℓr})
Frozen-Stop Δ .stableT _ _ = refl
Frozen-Stop Δ .confine (_ , sVis refl ())

-- DELETION: a frozen component may be replaced by `Stop`, whose force is a closed
-- constant — so a downstream refinement proof never tracks the component's state.
frozen-delete-⊑F : ∀ {ℓr} (A : EventSet) (Δ : (at : AnyTypes E) → proj₁ at → Set)
                 → (∀ {X : Set ℓ} {f : E X} {a : X} → Δ (X , f) a → A .mem (X , f) a)
                 → (P Rest D : PTree E (ExtI E) (⊤ {ℓr}))
                 → Frozen Δ P → Partner Δ A D
                 → ((Stop ⦀ Rest) ∥⇘ A ⇙ D) ⊑F ((P ⦀ Rest) ∥⇘ A ⇙ D)
frozen-delete-⊑F A Δ Δ⊆A P Rest D fP pd =
  frozen-swap-⊑F A Δ Δ⊆A P Stop fP (Frozen-Stop Δ) Rest D pd

-- REINSTATEMENT: the hypotheses are symmetric, so the refinement holds the other way
-- round too — the frozen component and `Stop` are `⊑F`-interchangeable.
frozen-reinstate-⊑F : ∀ {ℓr} (A : EventSet) (Δ : (at : AnyTypes E) → proj₁ at → Set)
                    → (∀ {X : Set ℓ} {f : E X} {a : X} → Δ (X , f) a → A .mem (X , f) a)
                    → (P Rest D : PTree E (ExtI E) (⊤ {ℓr}))
                    → Frozen Δ P → Partner Δ A D
                    → ((P ⦀ Rest) ∥⇘ A ⇙ D) ⊑F ((Stop ⦀ Rest) ∥⇘ A ⇙ D)
frozen-reinstate-⊑F A Δ Δ⊆A P Rest D fP pd =
  frozen-swap-⊑F A Δ Δ⊆A Stop P (Frozen-Stop Δ) fP Rest D pd

-------------------------------------------------------------------------------------
-- §5.  Introduction kit for `Partner`.  Both directions of the invariant are pointwise
--      in the partner's offers, so they distribute over `⦀` — which is what a real
--      driver bundle (`produce ⦀ produce`) needs.  `Partner-Stop` and `Partner-Ret`
--      are the leaves.
-------------------------------------------------------------------------------------

-- `Stop` offers nothing, so it is a partner for every `Δ` and `A`
Partner-Stop : ∀ {ℓr} (Δ : (at : AnyTypes E) → proj₁ at → Set) (A : EventSet)
             → Partner Δ A (Stop {ℓr})
Partner-Stop Δ A .avoid  _ (_ , sVis refl ())
Partner-Stop Δ A .inside   (_ , sVis refl ())
Partner-Stop Δ A .next (sRet ())
Partner-Stop Δ A .next (sSil ())
Partner-Stop Δ A .next (sVis refl ())
Partner-Stop Δ A .next (sTau refl ())
