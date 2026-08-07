{-# OPTIONS --guardedness #-}

-- Failures-divergences law-suite for the THROW operator `_⟦_▷_`
-- (Roscoe  P [|A|> Q).  Three laws:
--
--   Θ-Pret-≈    : force P ≡ ret r ⇒ (P ⟦ A ▷ Q) ≈FD P
--                 (P terminates immediately; the throw never fires — its force IS P's
--                  force, both `ret r`, so they are strongly bisimilar.)
--   Θ-div-row   : Diverges P ⇒ (P ⟦ A ▷ Q) ≈FD P
--                 (P root-diverges; P's τ lifts through the throw, so P ⟦ A ▷ Q also
--                  root-diverges — both are ⊥ in the FD model.)
--   Θ-⊓L-dist   : (P₁ ⊓ P₂) ⟦ A ▷ Q ≈FD (P₁ ⟦ A ▷ Q) ⊓ (P₂ ⟦ A ▷ Q)
--                 (left-⊓ distributivity.  At the ⊓-node force P offers ∅v visibly
--                  and `br2 P₁ P₂` for τ; throw weaves ONLY on P's structure, so the
--                  τ-targets are exactly P₁ ⟦ A ▷ Q / P₂ ⟦ A ▷ Q — the same as the RHS's
--                  br2.  A STRONG bisimulation, unlike interrupt which weaves Q here.)
--
-- All three reduce (via sbisim→drbisim ∘ drbisim→≈FD, or root-div→≈FD) to a strong
-- bisimulation or a root-divergence; no König / bar-induction step is needed.

open import Level using (Level; Lift; lift; lower)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Unit using () renaming (tt to tt0)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.ThrowFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Bisim               {E = E} {I = ExtI E}
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges; deadlock-converges; deadlock-no-τ)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (deadlock-no-offer; Refuses; Offers)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_≈FD_; _⊑D_; _⊑F⊥_; _⊑FD_; IsDivergence; divergences; div-extension-closed; failures⊥)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD        {E = E} {I = ExtI E}
  using (drbisim→≈FD; stable-not-ret; stable-react-τc; mk-stable)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
  using (force-Θ-ret; force-Θ-react; force-Θ-sil;
         Θ-τ-elim; Θ-ev-elim; ΘevR; Θthrow; Θpass; Θdone)
-- the Throw intro-step and divergence lemmas were HOISTED to the trace layer (so the
-- FSim layer can reuse them without this module's closure); re-exported `public` here so
-- that every previous client of `ThrowFD` still sees exactly the same names.
open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
  using (Θ-τ-lift-P; Θ-Diverges-L; Θ-div-step; Θ-Diverges→;
         Θ-throw-step; Θ-pass-step) public
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-div→; ⊓-div←l; ⊓-div←r;
         ⊓-failures→; ⊓-failures←l; ⊓-failures←r;
         ⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r)

open EventSet

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- Self-contained helpers (copied from InterruptFD): force-eq ⇒ Sbisim, and the two
-- root-divergence lemmas behind the DIV row.
-------------------------------------------------------------------------------------

-- two trees with equal `force` are strongly bisimilar: every step is determined by
-- `force`, so it transports across the equality to the SAME target.
sbisim-force-eq : {t u : PTree E (ExtI E) R}
                → PTree.force t ≡ PTree.force u → Sbisim R t u
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-ev  (sRet feq)    = _ , sRet (trans (sym eq) feq) , sbisim-refl _
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-ev  (sVis feq br) = _ , sVis (trans (sym eq) feq) br , sbisim-refl _
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-tau (sSil feq)    = _ , sSil (trans (sym eq) feq) , sbisim-refl _
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-tau (sTau feq br) = _ , sTau (trans (sym eq) feq) br , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-ev  (sRet feq)    = _ , sRet (trans eq feq) , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-ev  (sVis feq br) = _ , sVis (trans eq feq) br , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-tau (sSil feq)    = _ , sSil (trans eq feq) , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-tau (sTau feq br) = _ , sTau (trans eq feq) br , sbisim-refl _

-- a root-divergent process diverges on EVERY trace (take the empty prefix).
root-div→all-div : {P : PTree E (ExtI E) R} {s : List (Event√ R)}
                 → Diverges P → divergences P s
root-div→all-div {P = P} {s = s} divP = record
  { prefix  = []
  ; suffix  = s
  ; split   = refl
  ; witness = P
  ; reach   = ⟹-refl
  ; divwit  = divP
  }

-- two root-divergent processes are FD-equivalent (both ⊥): every refusal/divergence
-- claim is discharged by the divergence summand of failures⊥ and by all-div for ⊑D.
root-div→≈FD : {P Q : PTree E (ExtI E) R}
             → Diverges P → Diverges Q → P ≈FD Q
root-div→≈FD {P = P} {Q = Q} divP divQ =
  ( ( (λ _ → inj₂ (root-div→all-div divP))
    , (λ _ → root-div→all-div divP) )
  , ( (λ _ → inj₂ (root-div→all-div divQ))
    , (λ _ → root-div→all-div divQ) ) )

-------------------------------------------------------------------------------------
-- LAW 1: the RET row.  force P ≡ ret r ⇒ force (P ⟦ A ▷ Q) ≡ ret r ≡ force P, so the
-- throw and P are strongly bisimilar.
-------------------------------------------------------------------------------------

Θ-Pret-≈ : {P Q : PTree E (ExtI E) R} {A : EventSet} {r : R}
         → PTree.force P ≡ ret r → (P ⟦ A ▷ Q) ≈FD P
Θ-Pret-≈ {P = P} {Q = Q} {A = A} eqP =
  drbisim→≈FD (sbisim→drbisim
    (sbisim-force-eq (trans (force-Θ-ret {P = P} {Q = Q} {A = A} eqP) (sym eqP))))

-------------------------------------------------------------------------------------
-- LAW 2: the DIV row.  P's τ lifts through the throw, so Diverges P ⇒ Diverges (P⟦A▷Q);
-- both root-diverge ⇒ ≈FD.
-------------------------------------------------------------------------------------

Θ-div-row : {P Q : PTree E (ExtI E) R} {A : EventSet}
          → Diverges P → (P ⟦ A ▷ Q) ≈FD P
Θ-div-row {P = P} {Q = Q} {A = A} divP =
  root-div→≈FD (Θ-Diverges-L {P = P} {Q = Q} {A = A} divP) divP

-------------------------------------------------------------------------------------
-- LAW 3: left-⊓ distributivity.  STRONG bisimulation.
--
-- force (P₁ ⊓ P₂) = react ∅v (br2 P₁ P₂).  So
--   force ((P₁ ⊓ P₂) ⟦ A ▷ Q) = react (Θ-vis A (react ∅v (br2 P₁ P₂)) Q)
--                                     (Θ-τ  A (react ∅v (br2 P₁ P₂)) Q)
-- The vis part reads viewV (react ∅v …) = ∅v ⇒ everywhere nothing (no visible step).
-- The τ part reads viewT (react ∅v (br2 P₁ P₂)) = br2 P₁ P₂ ⇒ at (_,fin)(lift fzero)
-- just (P₁ ⟦ A ▷ Q), at (lift (fsuc fzero)) just (P₂ ⟦ A ▷ Q), else nothing.
--
-- force ((P₁ ⟦ A ▷ Q) ⊓ (P₂ ⟦ A ▷ Q)) = react ∅v (br2 (P₁ ⟦ A ▷ Q) (P₂ ⟦ A ▷ Q))
-- — SAME τ-targets at the SAME indices, ∅v visible.  Match the steps directly.
-------------------------------------------------------------------------------------

-- a `just M` out of the LHS τ-branch (Θ-τ over the ⊓-node) is P₁⟦A▷Q (tag0) or
-- P₂⟦A▷Q (tag1).  (Mirrors br2-source: viewT (react ∅v (br2 P₁ P₂)) = br2 P₁ P₂.)
Θ-⊓-τ-source : (P₁ P₂ Q : PTree E (ExtI E) R) (A : EventSet)
                 {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
             → Θ-τ A (react ∅v (br2 P₁ P₂)) Q i a ≡ just M
             → (M ≡ (P₁ ⟦ A ▷ Q)) ⊎ (M ≡ (P₂ ⟦ A ▷ Q))
Θ-⊓-τ-source P₁ P₂ Q A {_ , base _}   eq = case eq of λ ()
Θ-⊓-τ-source P₁ P₂ Q A {_ , pair _ _} eq = case eq of λ ()
Θ-⊓-τ-source P₁ P₂ Q A {_ , fin} {a = lift fzero}            eq = inj₁ (sym (just-injective eq))
Θ-⊓-τ-source P₁ P₂ Q A {_ , fin} {a = lift (fsuc fzero)}     eq = inj₂ (sym (just-injective eq))
Θ-⊓-τ-source P₁ P₂ Q A {_ , fin} {a = lift (fsuc (fsuc _))}  eq = case eq of λ ()

-- a `just M` out of the RHS br2 node is P₁⟦A▷Q (tag0) or P₂⟦A▷Q (tag1).
⊓-br2-source : (X Y : PTree E (ExtI E) R)
                 {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
             → br2 X Y i a ≡ just M → (M ≡ X) ⊎ (M ≡ Y)
⊓-br2-source X Y {_ , base _}   eq = case eq of λ ()
⊓-br2-source X Y {_ , pair _ _} eq = case eq of λ ()
⊓-br2-source X Y {_ , fin} {a = lift fzero}            eq = inj₁ (sym (just-injective eq))
⊓-br2-source X Y {_ , fin} {a = lift (fsuc fzero)}     eq = inj₂ (sym (just-injective eq))
⊓-br2-source X Y {_ , fin} {a = lift (fsuc (fsuc _))}  eq = case eq of λ ()

-- the strong bisimulation.  Both forces are `react ∅v <τ-fn>`; the τ-functions agree
-- pointwise (both give Pᵢ⟦A▷Q), so a τ-step of one matches a τ-step of the other to
-- the SAME target.  Visible parts are ∅v ⇒ no visible step (on-ev vacuous).
Θ-⊓L-sbisim : (P₁ P₂ Q : PTree E (ExtI E) R) (A : EventSet)
            → Sbisim R ((P₁ ⊓ P₂) ⟦ A ▷ Q) ((P₁ ⟦ A ▷ Q) ⊓ (P₂ ⟦ A ▷ Q))
-- LHS visible step: force LHS ≡ react (Θ-vis … over ⊓) (Θ-τ …); the vis offer is
-- viewV (react ∅v …) = ∅v ⇒ nothing, so `breq : ∅v at a ≡ just _` is absurd.
Θ-⊓L-sbisim P₁ P₂ Q A .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} {t′ = M} eqf breq) =
  -- force LHS reduces to react (Θ-vis A (react ∅v (br2 P₁ P₂)) Q) …; the vis offer reads
  -- viewV (react ∅v …) at a = ∅v at a = nothing, so the re-typed breq is `nothing ≡ just M`.
  case (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) breq) of λ ()
-- LHS τ-step: it reads Θ-τ A (react ∅v (br2 P₁ P₂)) Q i a ≡ just M; the source is
-- Pᵢ⟦A▷Q.  Produce the matching RHS τ (br2 tag) to the SAME target.
Θ-⊓L-sbisim P₁ P₂ Q A .Sbisim.fwd .SSimF.on-tau (sTau {i = i} {a = a} {t′ = M} eqf breq)
  -- force LHS reduces definitionally to react (Θ-vis …) (Θ-τ A (react ∅v (br2 P₁ P₂)) Q);
  -- react-injective re-types breq onto that known τ-function.
  with Θ-⊓-τ-source P₁ P₂ Q A {i = i} {a = a}
         (subst (λ g → g i a ≡ just M) (sym (proj₂ (react-injective eqf))) breq)
... | inj₁ refl = _ , sTau {i = _ , fin {n = 2}} {a = lift fzero}        refl refl , sbisim-refl _
... | inj₂ refl = _ , sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl , sbisim-refl _
-- a τ from a `sil` would need force LHS ≡ sil _, but it is react — absurd.
Θ-⊓L-sbisim P₁ P₂ Q A .Sbisim.fwd .SSimF.on-tau (sSil eqf) = case eqf of λ ()
-- RHS visible step: force RHS ≡ react ∅v (br2 …); vis offer ∅v ⇒ nothing, absurd.
Θ-⊓L-sbisim P₁ P₂ Q A .Sbisim.bwd .SSimF.on-ev (sVis {at = at} {a = a} {t′ = M} eqf breq) =
  -- force RHS reduces to react ∅v (br2 …); the vis offer is ∅v at a = nothing.
  case (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) breq) of λ ()
-- RHS τ-step: reads br2 (P₁⟦A▷Q) (P₂⟦A▷Q) i a ≡ just M; source Pᵢ⟦A▷Q.  Produce the
-- matching LHS τ (the throw's τ over the ⊓-node, same br2 index) to the SAME target.
Θ-⊓L-sbisim P₁ P₂ Q A .Sbisim.bwd .SSimF.on-tau (sTau {i = i} {a = a} {t′ = M} eqf breq)
  -- force RHS reduces definitionally to react ∅v (br2 (P₁⟦A▷Q) (P₂⟦A▷Q)); re-type breq.
  with ⊓-br2-source (P₁ ⟦ A ▷ Q) (P₂ ⟦ A ▷ Q) {i = i} {a = a}
         (subst (λ g → g i a ≡ just M) (sym (proj₂ (react-injective eqf))) breq)
... | inj₁ refl = _ , sTau {i = _ , fin {n = 2}} {a = lift fzero}
                          (force-Θ-react {P = P₁ ⊓ P₂} {Q = Q} {A = A} refl) refl
                   , sbisim-refl _
... | inj₂ refl = _ , sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)}
                          (force-Θ-react {P = P₁ ⊓ P₂} {Q = Q} {A = A} refl) refl
                   , sbisim-refl _
Θ-⊓L-sbisim P₁ P₂ Q A .Sbisim.bwd .SSimF.on-tau (sSil eqf) = case eqf of λ ()

Θ-⊓L-dist-FD : (P₁ P₂ Q : PTree E (ExtI E) R) (A : EventSet)
             → ((P₁ ⊓ P₂) ⟦ A ▷ Q) ≈FD ((P₁ ⟦ A ▷ Q) ⊓ (P₂ ⟦ A ▷ Q))
Θ-⊓L-dist-FD P₁ P₂ Q A =
  drbisim→≈FD (sbisim→drbisim (Θ-⊓L-sbisim P₁ P₂ Q A))

-------------------------------------------------------------------------------------
-- LAW 4: right-⊓ distributivity, divergence half.
--
--   LHS = P ⟦ A ▷ (Q₁ ⊓ Q₂)      RHS = (P ⟦ A ▷ Q₁) ⊓ (P ⟦ A ▷ Q₂)
--
-- KÖNIG-FREE.  Throw's only τ-moves come from P (Θ-τ lifts P's τ); the handler X is
-- dormant until a visible A-event FIRES the throw.  A divergence of `P ⟦ A ▷ X` is
-- either P diverging (no fire) or it fires on an A-event then diverges in X — never
-- both operands at once.  So `Θ-Diverges→` is a clean structural copattern (no König,
-- no postulate), unlike `△-Diverges→`.
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
-- (1) structural Θ-Diverges→ (the only τ-targets of P ⟦ A ▷ Q are P′ ⟦ A ▷ Q, i.e. P's
--     τ's), Θ-Diverges-L / Θ-τ-lift-P, and (2) the intro steps Θ-throw-step / Θ-pass-step
--     (the forward analogues of Θthrow / Θpass) now live in `Part 4` of
--     `CSP.Laws.Traces.TraceLawsThrowInterrupt` and are RE-EXPORTED by the import above,
--     so this module's API is unchanged.  They were hoisted so that the FSim layer
--     (`CSP.Laws.FSim.ThrowCong`) can reuse them without importing this whole law-suite.
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
-- (3) divergence-record plumbing (small copies of the InterruptFD versions).
-------------------------------------------------------------------------------------

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

mk-div-from : {P W : PTree E (ExtI E) R} {pre : List (Event√ R)}
            → P ⟹⟨ pre ⟩ W → Diverges W → divergences P pre
mk-div-from {pre = pre} reach divw = record
  { prefix = pre ; suffix = [] ; split = sym (++-identityʳ pre)
  ; witness = _ ; reach = reach ; divwit = divw }

-------------------------------------------------------------------------------------
-- (4) the EASY half:  LHS = P⟦A▷(Q₁⊓Q₂) simulates RHS = (P⟦A▷Q₁)⊓(P⟦A▷Q₂).
-- A handler-monotonicity worker maps a divergence of P⟦A▷Qᵢ to one of P⟦A▷(Q₁⊓Q₂),
-- by induction on the divergence's big-step reach.  (Qᵢ enters only via Θthrow, where
-- divergences Qᵢ ⇒ divergences (Q₁⊓Q₂) via ⊓-div←l/r.)
-------------------------------------------------------------------------------------

Θ-handler-mono-reach : (P Qᵢ Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
                         (route : ∀ {s} → divergences Qᵢ s → divergences (Q₁ ⊓ Q₂) s)
                         {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
                     → (P ⟦ A ▷ Qᵢ) ⟹⟨ pre ⟩ W → Diverges W
                     → divergences (P ⟦ A ▷ (Q₁ ⊓ Q₂)) pre
-- base: Diverges (P⟦A▷Qᵢ) ⇒ Diverges P ⇒ Diverges (P⟦A▷(Q₁⊓Q₂)).
Θ-handler-mono-reach P Qᵢ Q₁ Q₂ A route ⟹-refl divW =
  root-div→all-div (Θ-Diverges-L {P = P} {Q = Q₁ ⊓ Q₂} {A = A}
                                 (Θ-Diverges→ {P = P} {Q = Qᵢ} {A = A} divW))
-- τ-step: P's τ (Θ-τ-elim); recurse, prepend via Θ-τ-lift-P.
Θ-handler-mono-reach P Qᵢ Q₁ Q₂ A route (⟹-τ step rest) divW
  with Θ-τ-elim P Qᵢ step
... | (P′ , sP , refl) =
      div-τ-prepend (Θ-τ-lift-P {P = P} {P′ = P′} {Q = Q₁ ⊓ Q₂} {A = A} sP)
                    (Θ-handler-mono-reach P′ Qᵢ Q₁ Q₂ A route rest divW)
-- ev-step: invert with Θ-ev-elim.
Θ-handler-mono-reach P Qᵢ Q₁ Q₂ A route (⟹-ev step rest) divW
  with Θ-ev-elim P Qᵢ step
-- Θthrow: M ≡ Qᵢ.  rest is a divergence-reach of Qᵢ ⇒ divergences (Q₁⊓Q₂) at pre;
-- prepend the fire-event via Θ-throw-step into P⟦A▷(Q₁⊓Q₂).
... | Θthrow {at = at} {a = a} sP m =
      div-ev-prepend
        (Θ-throw-step {P = P} {X = Q₁ ⊓ Q₂} {A = A} {at = at} {a = a} sP m)
        (route (mk-div-from rest divW))
-- Θpass: M ≡ P′⟦A▷Qᵢ; recurse, prepend Θ-pass-step.
... | Θpass {at = at} {a = a} {P₁ = P′} sP ¬m =
      div-ev-prepend
        (Θ-pass-step {P = P} {P′ = P′} {X = Q₁ ⊓ Q₂} {A = A} {at = at} {a = a} sP ¬m)
        (Θ-handler-mono-reach P′ Qᵢ Q₁ Q₂ A route rest divW)
-- Θdone: M ≡ deadlock; rest is a divergence-reach from deadlock — impossible.
-- deadlock has no steps, so the only reach is ⟹-refl (W ≡ deadlock); then Diverges
-- deadlock is absurd.  A leading τ / ev is refuted directly.
... | Θdone _ with rest
...   | ⟹-refl    = ⊥-elim (deadlock-converges divW)
...   | ⟹-τ st _  = ⊥-elim (deadlock-no-τ st)
...   | ⟹-ev st _ = ⊥-elim (deadlock-no-offer st)

Θ-handler-mono : (P Qᵢ Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
                   (route : ∀ {s} → divergences Qᵢ s → divergences (Q₁ ⊓ Q₂) s)
                   {s : List (Event√ R)}
               → divergences (P ⟦ A ▷ Qᵢ) s → divergences (P ⟦ A ▷ (Q₁ ⊓ Q₂)) s
Θ-handler-mono P Qᵢ Q₁ Q₂ A route d =
  subst (divergences (P ⟦ A ▷ (Q₁ ⊓ Q₂)))
        (sym (d .IsDivergence.split))
        (div-extension-closed
          (Θ-handler-mono-reach P Qᵢ Q₁ Q₂ A route
                                (d .IsDivergence.reach) (d .IsDivergence.divwit)))

Θ-⊓R-dist-⊑D : (P Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
             → (P ⟦ A ▷ (Q₁ ⊓ Q₂)) ⊑D ((P ⟦ A ▷ Q₁) ⊓ (P ⟦ A ▷ Q₂))
Θ-⊓R-dist-⊑D P Q₁ Q₂ A d with ⊓-div→ (P ⟦ A ▷ Q₁) (P ⟦ A ▷ Q₂) d
... | inj₁ dQ₁ = Θ-handler-mono P Q₁ Q₁ Q₂ A (⊓-div←l Q₁ Q₂) dQ₁
... | inj₂ dQ₂ = Θ-handler-mono P Q₂ Q₁ Q₂ A (⊓-div←r Q₁ Q₂) dQ₂

-------------------------------------------------------------------------------------
-- (5) the HARD half:  RHS simulates LHS, via a distribution-specific elim that splits
-- the handler at the fire.  Same induction; at Θthrow, ⊓-div→ on Q₁⊓Q₂ chooses the side.
-------------------------------------------------------------------------------------

Θ-⊓R-reach-div : (P Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
                   {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
               → (P ⟦ A ▷ (Q₁ ⊓ Q₂)) ⟹⟨ pre ⟩ W → Diverges W
               → divergences (P ⟦ A ▷ Q₁) pre ⊎ divergences (P ⟦ A ▷ Q₂) pre
-- base: Diverges (P⟦A▷(Q₁⊓Q₂)) ⇒ Diverges P ⇒ Diverges (P⟦A▷Q₁) ⇒ inj₁.
Θ-⊓R-reach-div P Q₁ Q₂ A ⟹-refl divW =
  inj₁ (root-div→all-div (Θ-Diverges-L {P = P} {Q = Q₁} {A = A}
                                       (Θ-Diverges→ {P = P} {Q = Q₁ ⊓ Q₂} {A = A} divW)))
-- τ-step: P's τ; recurse, prepend Θ-τ-lift-P to both sides.
Θ-⊓R-reach-div P Q₁ Q₂ A (⟹-τ step rest) divW
  with Θ-τ-elim P (Q₁ ⊓ Q₂) step
... | (P′ , sP , refl) with Θ-⊓R-reach-div P′ Q₁ Q₂ A rest divW
...   | inj₁ dP₁ = inj₁ (div-τ-prepend (Θ-τ-lift-P {P = P} {P′ = P′} {Q = Q₁} {A = A} sP) dP₁)
...   | inj₂ dP₂ = inj₂ (div-τ-prepend (Θ-τ-lift-P {P = P} {P′ = P′} {Q = Q₂} {A = A} sP) dP₂)
-- ev-step: invert with Θ-ev-elim.
Θ-⊓R-reach-div P Q₁ Q₂ A (⟹-ev step rest) divW
  with Θ-ev-elim P (Q₁ ⊓ Q₂) step
-- Θthrow: M ≡ Q₁⊓Q₂.  rest ⇒ divergences (Q₁⊓Q₂) pre; ⊓-div→ chooses the side;
-- prepend the fire-event Θ-throw-step into the chosen P⟦A▷Qᵢ.
... | Θthrow {at = at} {a = a} sP m with ⊓-div→ Q₁ Q₂ (mk-div-from rest divW)
...   | inj₁ dQ₁ = inj₁ (div-ev-prepend (Θ-throw-step {P = P} {X = Q₁} {A = A} {at = at} {a = a} sP m) dQ₁)
...   | inj₂ dQ₂ = inj₂ (div-ev-prepend (Θ-throw-step {P = P} {X = Q₂} {A = A} {at = at} {a = a} sP m) dQ₂)
-- Θpass: M ≡ P′⟦A▷(Q₁⊓Q₂); recurse, prepend Θ-pass-step to both.
Θ-⊓R-reach-div P Q₁ Q₂ A (⟹-ev step rest) divW | Θpass {at = at} {a = a} {P₁ = P′} sP ¬m
  with Θ-⊓R-reach-div P′ Q₁ Q₂ A rest divW
...   | inj₁ dP₁ = inj₁ (div-ev-prepend (Θ-pass-step {P = P} {P′ = P′} {X = Q₁} {A = A} {at = at} {a = a} sP ¬m) dP₁)
...   | inj₂ dP₂ = inj₂ (div-ev-prepend (Θ-pass-step {P = P} {P′ = P′} {X = Q₂} {A = A} {at = at} {a = a} sP ¬m) dP₂)
-- Θdone: M ≡ deadlock; the residual divergence is rooted at deadlock — impossible.
Θ-⊓R-reach-div P Q₁ Q₂ A (⟹-ev step rest) divW | Θdone _ with rest
... | ⟹-refl    = ⊥-elim (deadlock-converges divW)
... | ⟹-τ st _  = ⊥-elim (deadlock-no-τ st)
... | ⟹-ev st _ = ⊥-elim (deadlock-no-offer st)

Θ-⊓R-div-elim : (P Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet) {s : List (Event√ R)}
              → divergences (P ⟦ A ▷ (Q₁ ⊓ Q₂)) s
              → divergences (P ⟦ A ▷ Q₁) s ⊎ divergences (P ⟦ A ▷ Q₂) s
Θ-⊓R-div-elim P Q₁ Q₂ A d
  with Θ-⊓R-reach-div P Q₁ Q₂ A (d .IsDivergence.reach) (d .IsDivergence.divwit)
... | inj₁ dP₁ = inj₁ (subst (divergences (P ⟦ A ▷ Q₁)) (sym (d .IsDivergence.split))
                             (div-extension-closed dP₁))
... | inj₂ dP₂ = inj₂ (subst (divergences (P ⟦ A ▷ Q₂)) (sym (d .IsDivergence.split))
                             (div-extension-closed dP₂))

Θ-⊓R-dist-⊒D : (P Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
             → ((P ⟦ A ▷ Q₁) ⊓ (P ⟦ A ▷ Q₂)) ⊑D (P ⟦ A ▷ (Q₁ ⊓ Q₂))
Θ-⊓R-dist-⊒D P Q₁ Q₂ A d with Θ-⊓R-div-elim P Q₁ Q₂ A d
... | inj₁ dP₁ = ⊓-div←l (P ⟦ A ▷ Q₁) (P ⟦ A ▷ Q₂) dP₁
... | inj₂ dP₂ = ⊓-div←r (P ⟦ A ▷ Q₁) (P ⟦ A ▷ Q₂) dP₂

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- LAW 4: right-⊓ distributivity, FAILURES half + assembly.
--
--   LHS = P ⟦ A ▷ (Q₁ ⊓ Q₂)      RHS = (P ⟦ A ▷ Q₁) ⊓ (P ⟦ A ▷ Q₂)
--
-- The failures worker mirrors `Θ-⊓R-div-elim`/`Θ-handler-mono` ARM-FOR-ARM, with
-- `Refuses W X` for `Diverges W` and `failures`/`fail-*-prepend` for the divergence
-- plumbing.  The ONE structural difference is the `⟹-refl` base: a divergence at refl
-- needs `P ⟦ A ▷ · ` to diverge, but a *failure* at refl just needs a stable refusing
-- witness — and that refusal is HANDLER-INDEPENDENT (the offers / stability of
-- `P ⟦ A ▷ ·` are determined by `force P` and `A`, never by the handler).  So a refusal
-- of `P ⟦ A ▷ (Q₁⊓Q₂)` is also a refusal of `P ⟦ A ▷ Q₁`, discharging the base.
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

-- failure prependers (rebuild the witness through a leading step).
fail-τ-prepend : {P P′ : PTree E (ExtI E) R} {s : List (Event√ R)} {X : Event√ R → Set ℓr}
               → P ─[ τ ]─► P′ → failures P′ s X → failures P s X
fail-τ-prepend step (W , reach , ref) = W , ⟹-τ step reach , ref

fail-ev-prepend : {P P′ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)}
                  {X : Event√ R → Set ℓr}
                → P ─[ ev e ]─► P′ → failures P′ s X → failures P (e ∷ s) X
fail-ev-prepend step (W , reach , ref) = W , ⟹-ev step reach , ref

-------------------------------------------------------------------------------------
-- (F) the KEY new insight: offers & stability of `P ⟦ A ▷ ·` are HANDLER-INDEPENDENT.
-- Both `Θ-vis A nP X at a` and `Θ-vis A nP Y at a` are `nothing` exactly when
-- `viewV nP at a ≡ nothing` (handler enters only in the `just` branch, which we never
-- inspect for *whether* an event is offered).  Likewise `Θ-τ A nP X i a ≡ nothing`
-- ⟺ `viewT nP i a ≡ nothing`.  Hence `Refuses (P ⟦ A ▷ X) X'` transfers to
-- `Refuses (P ⟦ A ▷ Y) X'`.
-------------------------------------------------------------------------------------

-- stability transfer at a fixed `force P ≡ nP` (NonRet, so force = react (Θ-vis…)(Θ-τ…)):
-- the τ-function `Θ-τ A nP Y` is everywhere nothing whenever `Θ-τ A nP X` is.
Θ-τ-nothing-indep : (nP : NodeKind E (ExtI E) R) (A : EventSet) (X Y : PTree E (ExtI E) R)
                      {i : AnyTypes (ExtI E)} {a : proj₁ i}
                  → Θ-τ A nP X i a ≡ nothing → Θ-τ A nP Y i a ≡ nothing
Θ-τ-nothing-indep nP A X Y {i = i} {a = a} eq with viewT nP i a
... | just _  = case eq of λ ()
... | nothing = refl

-- a `just` offer of `Θ-vis A nP X` at `a` forces `viewV nP at a ≡ just P'`, giving a
-- `just` offer of `Θ-vis A nP Y` at the SAME `a` (target may differ).
Θ-vis-just-indep : (nP : NodeKind E (ExtI E) R) (A : EventSet) (X Y : PTree E (ExtI E) R)
                     {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
                 → Θ-vis A nP X at a ≡ just M
                 → Σ[ M′ ∈ PTree E (ExtI E) R ] (Θ-vis A nP Y at a ≡ just M′)
Θ-vis-just-indep nP A X Y {at = at} {a = a} eq with viewV nP at a
... | nothing = case eq of λ ()
... | just P′ with A .dec at a
...   | yes _ = Y , refl
...   | no  _ = (P′ ⟦ A ▷ Y) , refl

-- stability of `P ⟦ A ▷ X` (NonRet P ⇒ react node) ⇒ stability of `P ⟦ A ▷ Y`.
Θ-isStable-indep : (P X Y : PTree E (ExtI E) R) (A : EventSet)
                     {nP : NodeKind E (ExtI E) R}
                 → PTree.force P ≡ nP
                 → isStable (P ⟦ A ▷ X) → isStable (P ⟦ A ▷ Y)
Θ-isStable-indep P X Y A {nP = ret r} eqP stX =
  -- force (P⟦A▷X) ≡ ret r ⇒ not stable
  ⊥-elim (stable-not-ret {t = P ⟦ A ▷ X} stX (force-Θ-ret {P = P} {Q = X} {A = A} eqP))
Θ-isStable-indep P X Y A {nP = sil P₁} eqP stX =
  mk-stable {t = P ⟦ A ▷ Y} (force-Θ-sil {P = P} {Q = Y} {A = A} eqP)
            (λ i a → Θ-τ-nothing-indep (sil P₁) A X Y {i = i} {a = a}
                       (stable-react-τc {t = P ⟦ A ▷ X} stX (force-Θ-sil {P = P} {Q = X} {A = A} eqP) i a))
Θ-isStable-indep P X Y A {nP = react v τc} eqP stX =
  mk-stable {t = P ⟦ A ▷ Y} (force-Θ-react {P = P} {Q = Y} {A = A} eqP)
            (λ i a → Θ-τ-nothing-indep (react v τc) A X Y {i = i} {a = a}
                       (stable-react-τc {t = P ⟦ A ▷ X} stX (force-Θ-react {P = P} {Q = X} {A = A} eqP) i a))

-- an offer of `P ⟦ A ▷ Y` (P NonRet) transports to an offer of `P ⟦ A ▷ X` at the SAME
-- event.  We key on the KNOWN react-shape of `force (P⟦A▷Y)` (force-Θ-sil/-react) to
-- re-type the `sVis` offer, swap the handler via Θ-vis-just-indep, then rebuild on X.
-- The sRet branch (force(P⟦A▷Y))≡ret) contradicts the known react-shape.
Θ-Offers-indep-sil : (P X Y : PTree E (ExtI E) R) (A : EventSet)
                       {P₁ : PTree E (ExtI E) R} {e : Event√ R}
                   → PTree.force P ≡ sil P₁
                   → Offers (P ⟦ A ▷ Y) e → Offers (P ⟦ A ▷ X) e
Θ-Offers-indep-sil P X Y A {P₁ = P₁} eqP (M , sVis {at = at} {a = a} eqfY brY)
  with Θ-vis-just-indep (sil P₁) A Y X {at = at} {a = a}
         (subst (λ g → g at a ≡ just M)
                (sym (proj₁ (react-injective
                       (trans (sym (force-Θ-sil {P = P} {Q = Y} {A = A} eqP)) eqfY)))) brY)
... | (M′ , offX) = M′ , sVis {at = at} {a = a}
                              (force-Θ-sil {P = P} {Q = X} {A = A} eqP) offX
Θ-Offers-indep-sil P X Y A {P₁ = P₁} eqP (M , sRet eqfY)
  = case trans (sym (force-Θ-sil {P = P} {Q = Y} {A = A} eqP)) eqfY of λ ()

Θ-Offers-indep-react : (P X Y : PTree E (ExtI E) R) (A : EventSet)
                        {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                        {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                        {e : Event√ R}
                    → PTree.force P ≡ react v τc
                    → Offers (P ⟦ A ▷ Y) e → Offers (P ⟦ A ▷ X) e
Θ-Offers-indep-react P X Y A {v = v} {τc = τc} eqP (M , sVis {at = at} {a = a} eqfY brY)
  with Θ-vis-just-indep (react v τc) A Y X {at = at} {a = a}
         (subst (λ g → g at a ≡ just M)
                (sym (proj₁ (react-injective
                       (trans (sym (force-Θ-react {P = P} {Q = Y} {A = A} eqP)) eqfY)))) brY)
... | (M′ , offX) = M′ , sVis {at = at} {a = a}
                              (force-Θ-react {P = P} {Q = X} {A = A} eqP) offX
Θ-Offers-indep-react P X Y A {v = v} {τc = τc} eqP (M , sRet eqfY)
  = case trans (sym (force-Θ-react {P = P} {Q = Y} {A = A} eqP)) eqfY of λ ()

-- force-shape trichotomy as PROPOSITIONAL equalities — lets us dispatch without a
-- `with PTree.force P` (which would reduce the `isStable (P⟦A▷·)` hypotheses' types).
Θ-force-tri : (P : PTree E (ExtI E) R)
            → (Σ[ r ∈ R ] (PTree.force P ≡ ret r))
            ⊎ (Σ[ P₁ ∈ PTree E (ExtI E) R ] (PTree.force P ≡ sil P₁))
            ⊎ (Σ[ v ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) ]
               Σ[ τc ∈ ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))) ]
                 (PTree.force P ≡ react v τc))
Θ-force-tri P with PTree.force P
... | ret r     = inj₁ (r , refl)
... | sil P₁    = inj₂ (inj₁ (P₁ , refl))
... | react v τc = inj₂ (inj₂ (v , τc , refl))

Θ-refuses-handler-indep : (P X Y : PTree E (ExtI E) R) (A : EventSet)
                            {X' : Event√ R → Set ℓr}
                        → Refuses (P ⟦ A ▷ X) X' → Refuses (P ⟦ A ▷ Y) X'
Θ-refuses-handler-indep P X Y A {X' = X'} (stX , noffX) with Θ-force-tri P
... | inj₁ (r , eqP) =
  -- force (P⟦A▷X) ≡ ret r ⇒ not stable ⇒ vacuous
  ⊥-elim (stable-not-ret {t = P ⟦ A ▷ X} stX (force-Θ-ret {P = P} {Q = X} {A = A} eqP))
... | inj₂ (inj₁ (P₁ , eqP)) =
  Θ-isStable-indep P X Y A {nP = sil P₁} eqP stX ,
  λ e xe offY → noffX e xe (Θ-Offers-indep-sil P X Y A {P₁ = P₁} eqP offY)
... | inj₂ (inj₂ (v , τc , eqP)) =
  Θ-isStable-indep P X Y A {nP = react v τc} eqP stX ,
  λ e xe offY → noffX e xe (Θ-Offers-indep-react P X Y A {v = v} {τc = τc} eqP offY)

-------------------------------------------------------------------------------------
-- (G) the distribution-specific stable-failures elimination (recursion on the
-- big-step).  SAME case split as `Θ-⊓R-reach-div` with `Refuses W X` for `Diverges W`.
-------------------------------------------------------------------------------------

Θ-⊓R-fail-elim : (P Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
                 {s : List (Event√ R)} {X : Event√ R → Set ℓr} {W : PTree E (ExtI E) R}
               → (P ⟦ A ▷ (Q₁ ⊓ Q₂)) ⟹⟨ s ⟩ W → Refuses W X
               → failures (P ⟦ A ▷ Q₁) s X ⊎ failures (P ⟦ A ▷ Q₂) s X
-- base: W ≡ P⟦A▷(Q₁⊓Q₂), Refuses it ⇒ Refuses (P⟦A▷Q₁) (handler-independent) ⇒ inj₁.
Θ-⊓R-fail-elim P Q₁ Q₂ A ⟹-refl ref =
  inj₁ (_ , ⟹-refl , Θ-refuses-handler-indep P (Q₁ ⊓ Q₂) Q₁ A ref)
-- τ-step: P's τ; recurse, prepend Θ-τ-lift-P to the chosen side.
Θ-⊓R-fail-elim P Q₁ Q₂ A (⟹-τ step rest) ref with Θ-τ-elim P (Q₁ ⊓ Q₂) step
... | (P′ , sP , refl) with Θ-⊓R-fail-elim P′ Q₁ Q₂ A rest ref
...   | inj₁ fP₁ = inj₁ (fail-τ-prepend (Θ-τ-lift-P {P = P} {P′ = P′} {Q = Q₁} {A = A} sP) fP₁)
...   | inj₂ fP₂ = inj₂ (fail-τ-prepend (Θ-τ-lift-P {P = P} {P′ = P′} {Q = Q₂} {A = A} sP) fP₂)
-- ev-step: invert with Θ-ev-elim.
Θ-⊓R-fail-elim P Q₁ Q₂ A (⟹-ev step rest) ref with Θ-ev-elim P (Q₁ ⊓ Q₂) step
-- Θthrow: M ≡ Q₁⊓Q₂.  rest+ref = failures (Q₁⊓Q₂) s X; ⊓-failures→ chooses the side;
-- prepend the fire-event Θ-throw-step into the chosen P⟦A▷Qᵢ.
... | Θthrow {at = at} {a = a} sP m with ⊓-failures→ Q₁ Q₂ (_ , rest , ref)
...   | inj₁ fQ₁ = inj₁ (fail-ev-prepend (Θ-throw-step {P = P} {X = Q₁} {A = A} {at = at} {a = a} sP m) fQ₁)
...   | inj₂ fQ₂ = inj₂ (fail-ev-prepend (Θ-throw-step {P = P} {X = Q₂} {A = A} {at = at} {a = a} sP m) fQ₂)
-- Θpass: M ≡ P′⟦A▷(Q₁⊓Q₂); recurse, prepend Θ-pass-step.
Θ-⊓R-fail-elim P Q₁ Q₂ A (⟹-ev step rest) ref | Θpass {at = at} {a = a} {P₁ = P′} sP ¬m
  with Θ-⊓R-fail-elim P′ Q₁ Q₂ A rest ref
...   | inj₁ fP₁ = inj₁ (fail-ev-prepend (Θ-pass-step {P = P} {P′ = P′} {X = Q₁} {A = A} {at = at} {a = a} sP ¬m) fP₁)
...   | inj₂ fP₂ = inj₂ (fail-ev-prepend (Θ-pass-step {P = P} {P′ = P′} {X = Q₂} {A = A} {at = at} {a = a} sP ¬m) fP₂)
-- Θdone: M ≡ deadlock with force P ≡ ret r.  force (P⟦A▷Qᵢ) ≡ ret r, so a √-step
-- (P⟦A▷Q₁) ─[ev (√ r)]→ deadlock exists (sRet); rest+ref = failures deadlock s X;
-- prepend the √-step ⇒ failures (P⟦A▷Q₁) (√r ∷ s) X.
Θ-⊓R-fail-elim P Q₁ Q₂ A (⟹-ev step rest) ref | Θdone {r = r} eqPr =
  inj₁ (fail-ev-prepend (sRet (force-Θ-ret {P = P} {Q = Q₁} {A = A} eqPr)) (_ , rest , ref))

-------------------------------------------------------------------------------------
-- (H) the two failures⊥ refinements.
-------------------------------------------------------------------------------------

-- a failures (P⟦A▷Qᵢ) s X maps to failures (P⟦A▷(Q₁⊓Q₂)) s X by the SAME structural
-- induction as Θ-handler-mono but on failures (the failures analogue of the easy half).
Θ-handler-mono-f-reach : (P Qᵢ Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
                           (route : ∀ {s} {X : Event√ R → Set ℓr}
                                   → failures Qᵢ s X → failures (Q₁ ⊓ Q₂) s X)
                           {s : List (Event√ R)} {X : Event√ R → Set ℓr} {W : PTree E (ExtI E) R}
                       → (P ⟦ A ▷ Qᵢ) ⟹⟨ s ⟩ W → Refuses W X
                       → failures (P ⟦ A ▷ (Q₁ ⊓ Q₂)) s X
-- base: Refuses (P⟦A▷Qᵢ) ⇒ Refuses (P⟦A▷(Q₁⊓Q₂)) (handler-independent).
Θ-handler-mono-f-reach P Qᵢ Q₁ Q₂ A route ⟹-refl ref =
  _ , ⟹-refl , Θ-refuses-handler-indep P Qᵢ (Q₁ ⊓ Q₂) A ref
-- τ-step: P's τ; recurse, prepend Θ-τ-lift-P.
Θ-handler-mono-f-reach P Qᵢ Q₁ Q₂ A route (⟹-τ step rest) ref with Θ-τ-elim P Qᵢ step
... | (P′ , sP , refl) =
      fail-τ-prepend (Θ-τ-lift-P {P = P} {P′ = P′} {Q = Q₁ ⊓ Q₂} {A = A} sP)
                     (Θ-handler-mono-f-reach P′ Qᵢ Q₁ Q₂ A route rest ref)
-- ev-step.
Θ-handler-mono-f-reach P Qᵢ Q₁ Q₂ A route (⟹-ev step rest) ref with Θ-ev-elim P Qᵢ step
-- Θthrow: M ≡ Qᵢ.  rest+ref = failures Qᵢ s X ⇒ failures (Q₁⊓Q₂) s X via route;
-- prepend the fire-event into P⟦A▷(Q₁⊓Q₂).
... | Θthrow {at = at} {a = a} sP m =
      fail-ev-prepend
        (Θ-throw-step {P = P} {X = Q₁ ⊓ Q₂} {A = A} {at = at} {a = a} sP m)
        (route (_ , rest , ref))
-- Θpass: M ≡ P′⟦A▷Qᵢ; recurse, prepend Θ-pass-step.
Θ-handler-mono-f-reach P Qᵢ Q₁ Q₂ A route (⟹-ev step rest) ref | Θpass {at = at} {a = a} {P₁ = P′} sP ¬m =
      fail-ev-prepend
        (Θ-pass-step {P = P} {P′ = P′} {X = Q₁ ⊓ Q₂} {A = A} {at = at} {a = a} sP ¬m)
        (Θ-handler-mono-f-reach P′ Qᵢ Q₁ Q₂ A route rest ref)
-- Θdone: M ≡ deadlock, force P ≡ ret r ⇒ force (P⟦A▷(Q₁⊓Q₂)) ≡ ret r ⇒ √-step.
Θ-handler-mono-f-reach P Qᵢ Q₁ Q₂ A route (⟹-ev step rest) ref | Θdone {r = r} eqPr =
      fail-ev-prepend (sRet (force-Θ-ret {P = P} {Q = Q₁ ⊓ Q₂} {A = A} eqPr)) (_ , rest , ref)

Θ-handler-mono-f : (P Qᵢ Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
                     (route : ∀ {s} {X : Event√ R → Set ℓr}
                             → failures Qᵢ s X → failures (Q₁ ⊓ Q₂) s X)
                     {s : List (Event√ R)} {X : Event√ R → Set ℓr}
                 → failures (P ⟦ A ▷ Qᵢ) s X → failures (P ⟦ A ▷ (Q₁ ⊓ Q₂)) s X
Θ-handler-mono-f P Qᵢ Q₁ Q₂ A route (W , reach , ref) =
  Θ-handler-mono-f-reach P Qᵢ Q₁ Q₂ A route reach ref

-- failures⊥ version of the handler-monotonicity worker (split the ⊎).
Θ-handler-mono-f⊥ : (P Qᵢ Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
                      (routeF : ∀ {s} {X : Event√ R → Set ℓr}
                              → failures Qᵢ s X → failures (Q₁ ⊓ Q₂) s X)
                      (routeD : ∀ {s} → divergences Qᵢ s → divergences (Q₁ ⊓ Q₂) s)
                      {s : List (Event√ R)} {B : Event√ R → Set ℓr}
                  → failures⊥ (P ⟦ A ▷ Qᵢ) s B → failures⊥ (P ⟦ A ▷ (Q₁ ⊓ Q₂)) s B
Θ-handler-mono-f⊥ P Qᵢ Q₁ Q₂ A routeF routeD (inj₁ f) =
  inj₁ (Θ-handler-mono-f P Qᵢ Q₁ Q₂ A routeF f)
Θ-handler-mono-f⊥ P Qᵢ Q₁ Q₂ A routeF routeD (inj₂ d) =
  inj₂ (Θ-handler-mono P Qᵢ Q₁ Q₂ A routeD d)

-- EASY (intro): a failures⊥ of (P⟦A▷Q₁)⊓(P⟦A▷Q₂) splits via ⊓-failures⊥→; map each
-- summand to a failures⊥ of P⟦A▷(Q₁⊓Q₂) via Θ-handler-mono-f⊥.
Θ-⊓R-dist-⊑F⊥ : (P Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
              → (P ⟦ A ▷ (Q₁ ⊓ Q₂)) ⊑F⊥ ((P ⟦ A ▷ Q₁) ⊓ (P ⟦ A ▷ Q₂))
Θ-⊓R-dist-⊑F⊥ P Q₁ Q₂ A f with ⊓-failures⊥→ (P ⟦ A ▷ Q₁) (P ⟦ A ▷ Q₂) f
... | inj₁ fQ₁ = Θ-handler-mono-f⊥ P Q₁ Q₁ Q₂ A (⊓-failures←l Q₁ Q₂) (⊓-div←l Q₁ Q₂) fQ₁
... | inj₂ fQ₂ = Θ-handler-mono-f⊥ P Q₂ Q₁ Q₂ A (⊓-failures←r Q₁ Q₂) (⊓-div←r Q₁ Q₂) fQ₂

-- HARD (elim): a failures⊥ of P⟦A▷(Q₁⊓Q₂) routes through Θ-⊓R-fail-elim / Θ-⊓R-div-elim.
Θ-⊓R-dist-⊒F⊥ : (P Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
              → ((P ⟦ A ▷ Q₁) ⊓ (P ⟦ A ▷ Q₂)) ⊑F⊥ (P ⟦ A ▷ (Q₁ ⊓ Q₂))
Θ-⊓R-dist-⊒F⊥ P Q₁ Q₂ A (inj₁ (W , reach , ref)) with Θ-⊓R-fail-elim P Q₁ Q₂ A reach ref
... | inj₁ fP₁ = ⊓-failures⊥←l (P ⟦ A ▷ Q₁) (P ⟦ A ▷ Q₂) (inj₁ fP₁)
... | inj₂ fP₂ = ⊓-failures⊥←r (P ⟦ A ▷ Q₁) (P ⟦ A ▷ Q₂) (inj₁ fP₂)
Θ-⊓R-dist-⊒F⊥ P Q₁ Q₂ A (inj₂ d) with Θ-⊓R-div-elim P Q₁ Q₂ A d
... | inj₁ dP₁ = ⊓-failures⊥←l (P ⟦ A ▷ Q₁) (P ⟦ A ▷ Q₂) (inj₂ dP₁)
... | inj₂ dP₂ = ⊓-failures⊥←r (P ⟦ A ▷ Q₁) (P ⟦ A ▷ Q₂) (inj₂ dP₂)

-------------------------------------------------------------------------------------
-- (I) the law: pair the two ⊑F⊥ and the two ⊑D refinements.
-------------------------------------------------------------------------------------

Θ-⊓R-dist-FD : (P Q₁ Q₂ : PTree E (ExtI E) R) (A : EventSet)
             → (P ⟦ A ▷ (Q₁ ⊓ Q₂)) ≈FD ((P ⟦ A ▷ Q₁) ⊓ (P ⟦ A ▷ Q₂))
Θ-⊓R-dist-FD P Q₁ Q₂ A =
  (Θ-⊓R-dist-⊑F⊥ P Q₁ Q₂ A , Θ-⊓R-dist-⊑D P Q₁ Q₂ A) ,
  (Θ-⊓R-dist-⊒F⊥ P Q₁ Q₂ A , Θ-⊓R-dist-⊒D P Q₁ Q₂ A)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- LAW 5: the THROW PREFIX-STEP law (Roscoe's Θ-step for a prefix).
--
--   (e ⟶ P) ⟦ A ▷ Q  ≈FD  e ⟶ (λ x → if (AV,e) x ∈ A then Q else P x ⟦ A ▷ Q)
--
-- Both sides are STABLE pure-visible prefix nodes (the prefix τ-part is `∅t`, and the
-- throw's `Θ-τ` over that `∅t` node is everywhere `nothing`).  No τ-moves on either
-- side; we only match visible offers.  At an event `(at , a)`:
--   • LHS force = react (Θ-vis A (react (Prefix-cont e P) ∅t) Q) (Θ-τ …); the vis offer
--     reads viewV (react (Prefix-cont e P) ∅t) at a = Prefix-cont e P at a =
--       (E-≟ (AV,e) at) ? just (P a) : nothing.  When `just (P a)`, A .dec at a decides
--       throw (just Q) / pass (just (P a ⟦ A ▷ Q)).
--   • RHS force = react (Prefix-cont e <cont>) ∅t; the vis offer is
--       (E-≟ (AV,e) at) ? just (<cont> a) : nothing, with <cont> a = Θ-step-cont … a
--       reducing (same A .dec at a) to Q resp. P a ⟦ A ▷ Q — the SAME target.
-- So the offers coincide pointwise ⇒ a strong bisimulation ⇒ ≈FD.
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

-- The RHS prefix continuation (named, top-level, to avoid an awkward `case … of λ{…}`
-- in the law's TYPE).  At each `x : AV` it FIRES (→ Q) when the event is in A, else
-- PASSES (→ P x ⟦ A ▷ Q).  `(_ , e) : AnyTypes E` is the channel (proj₁ = AV).
Θ-step-cont : {AV : Set ℓ} (e : E AV) (P : AV → PTree E (ExtI E) R)
              (Q : PTree E (ExtI E) R) (A : EventSet) → AV → PTree E (ExtI E) R
Θ-step-cont e P Q A x =
  case A .dec (_ , e) x of λ { (yes _) → Q ; (no _) → (P x ⟦ A ▷ Q) }

module _ {AV : Set ℓ} (e : E AV) (P : AV → PTree E (ExtI E) R)
         (Q : PTree E (ExtI E) R) (A : EventSet) where

  private
    nP : NodeKind E (ExtI E) R
    nP = react (Prefix-cont e P) ∅t

    LHS RHS : PTree E (ExtI E) R
    LHS = (e ⟶ P) ⟦ A ▷ Q
    RHS = e ⟶ Θ-step-cont e P Q A

  -- LHS forces to the throw-over-prefix node (the prefix is NonRet ⇒ react).
  force-LHS : PTree.force LHS ≡ react (Θ-vis A nP Q) (Θ-τ A nP Q)
  force-LHS = force-Θ-react {P = e ⟶ P} {Q = Q} {A = A} refl

  -- RHS forces to the prefix node for the fire/pass continuation (definitional).
  force-RHS : PTree.force RHS ≡ react (Prefix-cont e (Θ-step-cont e P Q A)) ∅t
  force-RHS = refl

  -- The offer-relation: at each (at , a), an LHS `just M` produces an RHS `just M′`
  -- with `Sbisim M M′` — and they are in fact the SAME term, so `sbisim-refl`.  Keyed
  -- on `E-≟ (AV,e) at` (which both `Θ-vis`-via-`Prefix-cont` and the RHS `Prefix-cont`
  -- dispatch on), then on `A .dec at a` for the fire/pass decision.
  step-offer : (at : AnyTypes E) (a : proj₁ at) {M : PTree E (ExtI E) R}
             → Θ-vis A nP Q at a ≡ just M
             → Σ[ M′ ∈ PTree E (ExtI E) R ]
                 (Prefix-cont e (Θ-step-cont e P Q A) at a ≡ just M′ × Sbisim R M M′)
  step-offer at a br with E-≟ (AV , e) at
  step-offer .(AV , e) a br | yes refl with A .dec (AV , e) a
  ... | yes _ with refl ← br = Q          , refl , sbisim-refl Q
  ... | no  _ with refl ← br = (P a ⟦ A ▷ Q) , refl , sbisim-refl (P a ⟦ A ▷ Q)
  step-offer at a br | no _ = case br of λ ()

  -- the reverse offer-relation (RHS offer ⇒ matching LHS offer, same target).
  step-offer⁻ : (at : AnyTypes E) (a : proj₁ at) {M′ : PTree E (ExtI E) R}
              → Prefix-cont e (Θ-step-cont e P Q A) at a ≡ just M′
              → Σ[ M ∈ PTree E (ExtI E) R ]
                  (Θ-vis A nP Q at a ≡ just M × Sbisim R M M′)
  step-offer⁻ at a br with E-≟ (AV , e) at
  step-offer⁻ .(AV , e) a br | yes refl with A .dec (AV , e) a
  ... | yes _ with refl ← br = Q          , refl , sbisim-refl Q
  ... | no  _ with refl ← br = (P a ⟦ A ▷ Q) , refl , sbisim-refl (P a ⟦ A ▷ Q)
  step-offer⁻ at a br | no _ = case br of λ ()

  -- no τ on either side: the LHS τ-part is `Θ-τ A nP Q` which reads
  -- viewT (react (Prefix-cont e P) ∅t) = ∅t ⇒ nothing; the RHS τ-part is `∅t`.
  Θ-prefix-τ-LHS-⊥ : ∀ {t} → LHS ─[ τ ]─► t → ⊥
  Θ-prefix-τ-LHS-⊥ (sSil sile) = case trans (sym sile) force-LHS of λ ()
  Θ-prefix-τ-LHS-⊥ (sTau {i = i} {a = a} eqf br) =
    case (subst (λ g → g i a ≡ just _) (sym (proj₂ (react-injective (trans (sym force-LHS) eqf)))) br) of λ ()

  Θ-prefix-τ-RHS-⊥ : ∀ {u} → RHS ─[ τ ]─► u → ⊥
  Θ-prefix-τ-RHS-⊥ (sSil sile) = case sile of λ ()
  Θ-prefix-τ-RHS-⊥ (sTau {i = i} {a = a} eqf br) =
    case (subst (λ g → g i a ≡ just _) (sym (proj₂ (react-injective eqf))) br) of λ ()

  Θ-prefix-sbisim : Sbisim R LHS RHS
  -- fwd
  Θ-prefix-sbisim .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqf br)
    with refl ← trans (sym force-LHS) eqf
    with (M′ , eqRHS , rel) ← step-offer at a br =
      M′ , sVis {at = at} {a = a} force-RHS eqRHS , rel
  Θ-prefix-sbisim .Sbisim.fwd .SSimF.on-tau step = case Θ-prefix-τ-LHS-⊥ step of λ ()
  -- bwd
  Θ-prefix-sbisim .Sbisim.bwd .SSimF.on-ev (sVis {at = at} {a = a} eqf br)
    with refl ← trans (sym force-RHS) eqf
    with (M , eqLHS , rel) ← step-offer⁻ at a br =
      M , sVis {at = at} {a = a} force-LHS eqLHS , sbisim-sym rel
  Θ-prefix-sbisim .Sbisim.bwd .SSimF.on-tau step = case Θ-prefix-τ-RHS-⊥ step of λ ()

Θ-prefix-step : ∀ {ℓr} {R : Set ℓr} {AV : Set ℓ}
                (e : E AV) (P : AV → PTree E (ExtI E) R) (Q : PTree E (ExtI E) R) (A : EventSet)
              → ((e ⟶ P) ⟦ A ▷ Q)
                ≈FD (e ⟶ Θ-step-cont e P Q A)
Θ-prefix-step e P Q A =
  drbisim→≈FD (sbisim→drbisim (Θ-prefix-sbisim e P Q A))

-------------------------------------------------------------------------------------
-- LAW 5′: the THROW step law over the full prefix-CHOICE menu `pchoice v` (U7.6 proper:
--   (?x:A→P) ⟦B▷ Q = ?x:A→(P x⟦B▷Q ◁ x∉B ▷ Q),  A = any event SET, multi-channel).
--
-- The single-channel `Θ-prefix-step` is the instance `v = Prefix-cont e P`.  Here the
-- RHS menu is `pchoice (Θ-vis A (react v ∅t) Q)` — and `Θ-vis A (react v ∅t) Q` is
-- *exactly* the LHS's visible map, so unlike the single-channel proof NO `step-offer`
-- casing is needed: both sides offer through the SAME map (sbisim-refl), and neither has
-- a τ (the throw's `Θ-τ` over the pure-visible `react v ∅t` reads `viewT … = ∅t` = nothing).
-------------------------------------------------------------------------------------

module _ {ℓr} {R : Set ℓr}
         (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         (Q : PTree E (ExtI E) R) (A : EventSet) where

  private
    nPv : NodeKind E (ExtI E) R
    nPv = react v ∅t

    Vθ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
    Vθ = Θ-vis A nPv Q

    LHSm RHSm : PTree E (ExtI E) R
    LHSm = (pchoice v) ⟦ A ▷ Q
    RHSm = pchoice Vθ

    force-LHSm : PTree.force LHSm ≡ react Vθ (Θ-τ A nPv Q)
    force-LHSm = force-Θ-react {P = pchoice v} {Q = Q} {A = A} refl

    force-RHSm : PTree.force RHSm ≡ react Vθ ∅t
    force-RHSm = refl

    τ-LHSm-⊥ : ∀ {t} → LHSm ─[ τ ]─► t → ⊥
    τ-LHSm-⊥ (sSil sile) = case trans (sym sile) force-LHSm of λ ()
    τ-LHSm-⊥ (sTau {i = i} {a = a} eqf br) =
      case (subst (λ g → g i a ≡ just _)
                  (sym (proj₂ (react-injective (trans (sym force-LHSm) eqf)))) br) of λ ()

    τ-RHSm-⊥ : ∀ {u} → RHSm ─[ τ ]─► u → ⊥
    τ-RHSm-⊥ (sSil sile) = case trans (sym sile) force-RHSm of λ ()
    τ-RHSm-⊥ (sTau {i = i} {a = a} eqf br) =
      case (subst (λ g → g i a ≡ just _)
                  (sym (proj₂ (react-injective (trans (sym force-RHSm) eqf)))) br) of λ ()

    Θ-menu-sbisim : Sbisim R LHSm RHSm
    Θ-menu-sbisim .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqf br)
      with refl ← trans (sym force-LHSm) eqf =
        _ , sVis {at = at} {a = a} force-RHSm br , sbisim-refl _
    Θ-menu-sbisim .Sbisim.fwd .SSimF.on-tau step = case τ-LHSm-⊥ step of λ ()
    Θ-menu-sbisim .Sbisim.bwd .SSimF.on-ev (sVis {at = at} {a = a} eqf br)
      with refl ← trans (sym force-RHSm) eqf =
        _ , sVis {at = at} {a = a} force-LHSm br , sbisim-refl _
    Θ-menu-sbisim .Sbisim.bwd .SSimF.on-tau step = case τ-RHSm-⊥ step of λ ()

  -- (?x:A→P) ⟦ B ▷ Q  ≈FD  ?x:A→(P⟦B▷Q ◁ x∉B ▷ Q)        (menu version of U7.6)
  Θ-step-menu-FD : ((pchoice v) ⟦ A ▷ Q) ≈FD pchoice (Θ-vis A (react v ∅t) Q)
  Θ-step-menu-FD = drbisim→≈FD (sbisim→drbisim Θ-menu-sbisim)
