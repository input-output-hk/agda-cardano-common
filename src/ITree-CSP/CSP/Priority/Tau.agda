{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Priority Layer 3: the τ-NORMALISED priority operator `Priτ`.
--
-- Unlike Layer-2 `Pri` (which prioritises one node at a time, keeping τ's),
-- `Priτ` first COLLAPSES the internal (τ) activity to reach a stable visible
-- menu and only then prioritises — this is Roscoe's operational reading.
--
-- To make this DEFINABLE and PRODUCTIVE we drive it by a CONSTRUCTIVE
-- τ-normalisation certificate (see the CRITICAL OBSTRUCTION note): a *postulated*
-- divergence-freedom hypothesis does not reduce and cannot follow τ's.  The
-- certificate is a mixed inductive/coinductive structure:
--   * `τ-NormF t` (INDUCTIVE): finitely many τ's (sil or an enabled react-τc,
--     each pointed at CONSTRUCTIVELY) reach a settled node — `ret`, or a stable
--     react menu whose every visible residual carries a (coinductive) sub-cert.
--   * `τ-Norm t`  (COINDUCTIVE): wraps `τ-NormF t`, so guarded corecursion can
--     continue hereditarily into the visible residuals.
--
-- `Priτ` reduces: `priτF` recurses on the INDUCTIVE `τ-NormF` (terminating)
-- to build the settled head, corecursing (guarded by `react`) into the visible
-- residuals.  NO `dne`/`Classical` is used in the DEFINITION.  (Convenience
-- builders from a divergence-freedom hypothesis live below as dne-postulates,
-- certified in `CSP/Laws/ClassicalFromLEM.agda`; they are NOT used to define
-- `Priτ`.)
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Function using (case_of_)

open import Process_Trees

module CSP.Priority.Tau {ℓ ℓe} {E : Set ℓ → Set ℓe} where

open PTree

open import Semantics.PriOrder  {ℓ} {ℓe} {E}
open import Semantics.LTS       {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.WeakBisim {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Bisim     {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import CSP.Priority.Base        {ℓ} {ℓe} {E}

------------------------------------------------------------------------
-- The τ-normalisation certificate (mixed inductive/coinductive).
------------------------------------------------------------------------

-- forward declarations of the mutual certificate
data τ-NormF {ℓr} {R : Set ℓr} (t : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
record τ-Norm {ℓr} {R : Set ℓr} (t : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)

-- INDUCTIVE: a finite τ-collapse to a settled node.
data τ-NormF {ℓr} {R} t where
  -- settled: a return node
  nret  : ∀ {r : R} → PTree.force t ≡ ret r → τ-NormF t
  -- settled: a STABLE react menu (no τ); each visible residual normalises (coind.)
  nmenu : ∀ {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
            {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
        → PTree.force t ≡ react v τc
        → (∀ i a → τc i a ≡ nothing)
        → (∀ {at a t′} → v at a ≡ just t′ → τ-Norm t′)
        → τ-NormF t
  -- τ-step via `sil`: collapse and continue (inductive)
  nsil  : ∀ {t′ : PTree E (ExtI E) R} → PTree.force t ≡ sil t′ → τ-NormF t′ → τ-NormF t
  -- τ-step via an ENABLED react-τc branch (pointed at constructively): collapse
  ntau  : ∀ {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
            {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
            {i : AnyTypes (ExtI E)} {a : proj₁ i} {t′ : PTree E (ExtI E) R}
        → PTree.force t ≡ react v τc → τc i a ≡ just t′ → τ-NormF t′ → τ-NormF t

-- COINDUCTIVE wrapper: hereditary normalisation.
record τ-Norm {ℓr} {R} t where
  coinductive
  field force-norm : τ-NormF t

open τ-Norm public

------------------------------------------------------------------------
-- The operator.  `priτF` recurses on the INDUCTIVE certificate to build the
-- settled head; the guarded corecursion (`Priτ` under `react`) enters visible
-- residuals through the coinductive sub-certificate.
------------------------------------------------------------------------

-- forward declarations
Priτ      : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
            (t : PTree E (ExtI E) R) → τ-Norm t → PTree E (ExtI E) R
priτF     : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo) {t : PTree E (ExtI E) R}
          → τ-NormF t → NodeKind E (ExtI E) R
priτVis   : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
            (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
          → (∀ {at a t′} → v at a ≡ just t′ → τ-Norm t′)
          → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
priτVisAt : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
            (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
          → (∀ {at a t′} → v at a ≡ just t′ → τ-Norm t′)
          → (at : AnyTypes E) (a : proj₁ at)
          → (dm : Bool) (m : Maybe (PTree E (ExtI E) R)) → v at a ≡ m
          → Maybe (PTree E (ExtI E) R)

-- head node = collapse τ's, then the settled menu (τ pruned to none)
force (Priτ O t cert) = priτF O (force-norm cert)

priτF O (nret {r = r} eqf)          = ret r
priτF O (nmenu {v = v} eqf stb sub) = react (priτVis O v sub) (λ _ _ → nothing)
priτF O (nsil eqf n′)               = priτF O n′
priτF O (ntau eqf br n′)            = priτF O n′

-- stable menu: prune dominated offers; each survivor corecurses via `Priτ` + its
-- sub-certificate (the guarded call sits under `react` ▸ `priτVis` ▸ `just`).
priτVis O v sub at a = priτVisAt O v sub at a (dominated? O v (at ∙ a)) (v at a) refl
priτVisAt O v sub at a dm    nothing    meq = nothing
priτVisAt O v sub at a true  (just t′)  meq = nothing
priτVisAt O v sub at a false (just t′)  meq = just (Priτ O t′ (sub meq))

-- smoke test: `deadlock` is a stable empty menu ⇒ trivial certificate; `Priτ`
-- reduces to a react node end-to-end (exercises the operator productively).
cert-deadlock : ∀ {ℓr} {R : Set ℓr} → τ-Norm (deadlock {E = E} {I = ExtI E} {R = R})
force-norm cert-deadlock = nmenu refl (λ i a → refl) (λ ())

priτ-deadlock-smoke : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo) → PTree E (ExtI E) R
priτ-deadlock-smoke O = Priτ O deadlock cert-deadlock

------------------------------------------------------------------------
-- Agreement (easy τ law): `Priτ` collapses a leading τ.
------------------------------------------------------------------------

private
  -- sil ≢ ret at the node level (sil ≢ react is already in Process_Trees)
  sil≢ret : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R} {x : R}
          → sil t ≡ ret x → ⊥
  sil≢ret ()

-- a one-τ prefix: `force (τ→ P) = sil P`
τ→_ : ∀ {ℓr} {R : Set ℓr} → PTree E (ExtI E) R → PTree E (ExtI E) R
force (τ→ P) = sil P

-- lift a normalisation certificate through the τ-prefix (collapse that τ)
τ→cert : ∀ {ℓr} {R : Set ℓr} {P : PTree E (ExtI E) R} → τ-Norm P → τ-Norm (τ→ P)
force-norm (τ→cert c) = nsil refl (force-norm c)

-- transport a step across a `force`-equality (transitions depend only on force)
transEv : ∀ {ℓr} {R : Set ℓr} {Q₁ Q₂ : PTree E (ExtI E) R} {l : Event√ R} {t′}
        → PTree.force Q₁ ≡ PTree.force Q₂ → Q₁ ─[ ev l ]─► t′ → Q₂ ─[ ev l ]─► t′
transEv fe (sRet eqft)   = sRet (trans (sym fe) eqft)
transEv fe (sVis eqft br) = sVis (trans (sym fe) eqft) br

transTau : ∀ {ℓr} {R : Set ℓr} {Q₁ Q₂ : PTree E (ExtI E) R} {t′}
         → PTree.force Q₁ ≡ PTree.force Q₂ → Q₁ ─[ τ ]─► t′ → Q₂ ─[ τ ]─► t′
transTau fe (sSil eqft)    = sSil (trans (sym fe) eqft)
transTau fe (sTau eqft br) = sTau (trans (sym fe) eqft) br

-- equal `force` ⇒ weakly bisimilar (matched step-for-step, targets identical)
sameForce→≈ : ∀ {ℓr} {R : Set ℓr} {Q₁ Q₂ : PTree E (ExtI E) R}
            → PTree.force Q₁ ≡ PTree.force Q₂ → Q₁ ≈ Q₂
sameForce→≈ fe .Wbisim.fwd .WSimF.on-ev  step = _ , wev τ*-refl (transEv fe step) τ*-refl , wbisim-refl _
sameForce→≈ fe .Wbisim.fwd .WSimF.on-tau step = _ , wτ (τ*-step (transTau fe step) τ*-refl) , wbisim-refl _
sameForce→≈ fe .Wbisim.bwd .WSimF.on-ev  step = _ , wev τ*-refl (transEv (sym fe) step) τ*-refl , wbisim-refl _
sameForce→≈ fe .Wbisim.bwd .WSimF.on-tau step = _ , wτ (τ*-step (transTau (sym fe) step) τ*-refl) , wbisim-refl _

-- τ-absorption: `τ→ Q ≈ Q`
sil≈ : ∀ {ℓr} {R : Set ℓr} (Q : PTree E (ExtI E) R) → (τ→ Q) ≈ Q
sil≈ Q .Wbisim.fwd .WSimF.on-ev  (sVis eqft _) = ⊥-elim (sil≢react eqft)
sil≈ Q .Wbisim.fwd .WSimF.on-ev  (sRet eqft)   = ⊥-elim (sil≢ret eqft)
sil≈ Q .Wbisim.fwd .WSimF.on-tau (sSil eqft)   =
  Q , wτ τ*-refl , subst (λ z → z ≈ Q) (sil-injective eqft) (wbisim-refl Q)
sil≈ Q .Wbisim.fwd .WSimF.on-tau (sTau eqft _) = ⊥-elim (sil≢react eqft)
-- Q's steps are matched by `τ→ Q` after prepending its leading τ
sil≈ Q .Wbisim.bwd .WSimF.on-ev  step =
  _ , wev (τ*-step (sSil refl) τ*-refl) step τ*-refl , wbisim-refl _
sil≈ Q .Wbisim.bwd .WSimF.on-tau step =
  _ , wτ (τ*-step (sSil refl) (τ*-step step τ*-refl)) , wbisim-refl _

-- AGREEMENT: `Priτ` of a τ-prefixed process = one τ then `Priτ` of the body
-- (`force (Priτ O (τ→ P) (τ→cert c)) = priτF O (force-norm c) = force (Priτ O P c)`).
Priτ-τ : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
         (P : PTree E (ExtI E) R) (c : τ-Norm P)
       → Priτ O (τ→ P) (τ→cert c) ≈ (τ→ Priτ O P c)
Priτ-τ O P c = wbisim-trans (sameForce→≈ refl) (wbisim-sym (sil≈ (Priτ O P c)))

------------------------------------------------------------------------
-- Agreement with Layer-2 `Pri` on the τ-FREE fragment (strong bisim `∼`).
--
-- FALSE in general: on a SLIDE node (a `react` with BOTH visible offers AND an
-- enabled τc) `Pri` keeps the pre-τ maximal offers (τ non-urgent) while `Priτ`
-- collapses the τ and discards them (maximal progress / forward-ref PriHide).
-- They agree exactly on the τ-free fragment (every reachable react is stable).
------------------------------------------------------------------------

-- the τ-free fragment: every reachable react node is stable (no τc), coinductive
data τ-FreeF {ℓr} {R : Set ℓr} (t : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
record τ-Free {ℓr} {R : Set ℓr} (t : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)

data τ-FreeF {ℓr} {R} t where
  fret  : ∀ {r : R} → PTree.force t ≡ ret r → τ-FreeF t
  fmenu : ∀ {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
            {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
        → PTree.force t ≡ react v τc → (∀ i a → τc i a ≡ nothing)
        → (∀ {at a t′} → v at a ≡ just t′ → τ-Free t′) → τ-FreeF t

record τ-Free {ℓr} {R} t where
  coinductive
  field free : τ-FreeF t
open τ-Free public

-- a τ-free certificate is a fortiori a τ-normalisation certificate (menu-only)
free→cert  : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R} → τ-Free t → τ-Norm t
free→certF : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R} → τ-FreeF t → τ-NormF t
force-norm (free→cert τf)       = free→certF (free τf)
free→certF (fret eqf)           = nret eqf
free→certF (fmenu eqf stb sub)  = nmenu eqf stb (λ br → free→cert (sub br))

-- residual relation for the two menus (both dead, or both alive & bisimilar)
data MaybeRel {ℓr} {R : Set ℓr}
            : Maybe (PTree E (ExtI E) R) → Maybe (PTree E (ExtI E) R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  mnothing : MaybeRel nothing nothing
  mjust    : ∀ {p q} → p ∼ q → MaybeRel (just p) (just q)

mrel-sym : ∀ {ℓr} {R : Set ℓr} {mp mq : Maybe (PTree E (ExtI E) R)}
         → MaybeRel mp mq → MaybeRel mq mp
mrel-sym mnothing    = mnothing
mrel-sym (mjust p∼q) = mjust (sbisim-sym p∼q)

-- read off the matching alive offer
mrel-just : ∀ {ℓr} {R : Set ℓr} {mp mq : Maybe (PTree E (ExtI E) R)} {u}
          → MaybeRel mp mq → mp ≡ just u
          → Σ[ q ∈ PTree E (ExtI E) R ] (mq ≡ just q) × (u ∼ q)
mrel-just mnothing ()
mrel-just (mjust {p} {q} p∼q) eq = q , refl , subst (λ z → z ∼ q) (just-injective eq) p∼q

-- two `ret r` nodes are strongly bisimilar (both fire only √ to deadlock)
ret-∼ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R} {r : R}
      → PTree.force P ≡ ret r → PTree.force Q ≡ ret r → P ∼ Q
ret-∼ fP fQ .Sbisim.fwd .SSimF.on-ev  (sRet eqP)   = deadlock , sRet (trans fQ (trans (sym fP) eqP)) , sbisim-refl _
ret-∼ fP fQ .Sbisim.fwd .SSimF.on-ev  (sVis eqP _) = case trans (sym fP) eqP of λ ()
ret-∼ fP fQ .Sbisim.fwd .SSimF.on-tau (sSil eqP)   = case trans (sym fP) eqP of λ ()
ret-∼ fP fQ .Sbisim.fwd .SSimF.on-tau (sTau eqP _) = case trans (sym fP) eqP of λ ()
ret-∼ fP fQ .Sbisim.bwd .SSimF.on-ev  (sRet eqQ)   = deadlock , sRet (trans fP (trans (sym fQ) eqQ)) , sbisim-refl _
ret-∼ fP fQ .Sbisim.bwd .SSimF.on-ev  (sVis eqQ _) = case trans (sym fQ) eqQ of λ ()
ret-∼ fP fQ .Sbisim.bwd .SSimF.on-tau (sSil eqQ)   = case trans (sym fQ) eqQ of λ ()
ret-∼ fP fQ .Sbisim.bwd .SSimF.on-tau (sTau eqQ _) = case trans (sym fQ) eqQ of λ ()

-- one direction of a stable-menu simulation (τc empty ⇒ no τ; offers via MaybeRel)
menu-sim : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
             {VP VQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
         → PTree.force P ≡ react VP (λ _ _ → nothing)
         → PTree.force Q ≡ react VQ (λ _ _ → nothing)
         → (∀ at a → MaybeRel (VP at a) (VQ at a))
         → SSimF (Sbisim R) P Q
menu-sim fP fQ menu .SSimF.on-ev (sVis {at = at} {a = a} eqP brP)
  with mrel-just (menu at a)
         (subst (λ V → V at a ≡ just _) (sym (proj₁ (react-injective (trans (sym fP) eqP)))) brP)
... | q , mq≡ , u∼q = q , sVis fQ mq≡ , u∼q
menu-sim fP fQ menu .SSimF.on-ev  (sRet eqP)                   = case trans (sym fP) eqP of λ ()
menu-sim fP fQ menu .SSimF.on-tau (sSil eqP)                   = case trans (sym fP) eqP of λ ()
menu-sim fP fQ menu .SSimF.on-tau (sTau {i = i} {a = a} eqP brP) =
  case subst (λ T → T i a ≡ just _) (sym (proj₂ (react-injective (trans (sym fP) eqP)))) brP of λ ()

-- two stable react nodes with empty τc and MaybeRel-agreeing offers are ∼
react-menu-∼ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
                 {VP VQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             → PTree.force P ≡ react VP (λ _ _ → nothing)
             → PTree.force Q ≡ react VQ (λ _ _ → nothing)
             → (∀ at a → MaybeRel (VP at a) (VQ at a))
             → P ∼ Q
react-menu-∼ fP fQ menu .Sbisim.fwd = menu-sim fP fQ menu
react-menu-∼ fP fQ menu .Sbisim.bwd = menu-sim fQ fP (λ at a → mrel-sym (menu at a))

-- recover `isStable t` from a react node with everywhere-`nothing` τc
mkStable : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
             {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
         → PTree.force t ≡ react v τc → (∀ i a → τc i a ≡ nothing) → isStable t
mkStable {t = t} eqf stb with PTree.force t | eqf
... | react v τc | refl = stb

module _ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo) where

  -- `Pri` reductions (node-view, stuck-but-valid) — mirror PriorityAdequacy
  priForce-ret-eq : {t : PTree E (ExtI E) R} {fb : FinBr t}
                    (nP : NodeKind E (ExtI E) R) (eqf : PTree.force t ≡ nP)
                    (dec : Dec (isStable t)) {r : R}
                  → nP ≡ ret r → priForce O nP eqf fb dec ≡ ret r
  priForce-ret-eq (ret r)      eqf dec refl = refl
  priForce-ret-eq (sil c)      eqf dec ()
  priForce-ret-eq (react v τc) eqf dec ()

  fPri-ret : {t : PTree E (ExtI E) R} {fb : FinBr t} {r : R}
           → PTree.force t ≡ ret r → PTree.force (Pri O t fb) ≡ ret r
  fPri-ret {t = t} {fb = fb} eqft = priForce-ret-eq (PTree.force t) refl (stab? t fb) eqft

  priForce-yes-eq : {t : PTree E (ExtI E) R} {fb : FinBr t}
                    (nP : NodeKind E (ExtI E) R) (eqf : PTree.force t ≡ nP) {st : isStable t}
                    {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  → nP ≡ react v τc
                  → Σ[ eqf′ ∈ PTree.force t ≡ react v τc ]
                      priForce O nP eqf fb (yes st) ≡ react (priVis O v eqf′ fb) (λ _ _ → nothing)
  priForce-yes-eq (react v τc) eqf refl = eqf , refl
  priForce-yes-eq (ret r)      eqf ()
  priForce-yes-eq (sil c)      eqf ()

  -- reduce `force (Pri O t fb)` at a stable react node (cases `stab?` where
  -- `force (Pri …)` is in the goal, so the decision propagates) — cf. fPri-react
  fPri-menu : {t : PTree E (ExtI E) R}
              {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
              {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
              (eqf : PTree.force t ≡ react v τc) (fb : FinBr t) → isStable t
            → Σ[ eqf′ ∈ PTree.force t ≡ react v τc ]
                PTree.force (Pri O t fb) ≡ react (priVis O v eqf′ fb) (λ _ _ → nothing)
  fPri-menu {t = t} eqf fb st with stab? t fb
  ... | yes st′ = priForce-yes-eq (PTree.force t) refl {st = st′} eqf
  ... | no ¬st  = ⊥-elim (¬st st)

  -- invert a fired priτ-offer (LHS): `priτVisAt … ≡ just u` ⇒ offer + residual
  priτVisAt-just : {t : PTree E (ExtI E) R}
                   {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   (subτ : ∀ {at a t′} → v at a ≡ just t′ → τ-Norm t′)
                   {at : AnyTypes E} {a : proj₁ at} {u : PTree E (ExtI E) R}
                   (dm : Bool) (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                 → priτVisAt O v subτ at a dm m meq ≡ just u
                 → Σ[ t′ ∈ PTree E (ExtI E) R ] (dm ≡ false)
                     × Σ[ eva ∈ v at a ≡ just t′ ] (Priτ O t′ (subτ eva) ≡ u)
  priτVisAt-just subτ dm    nothing   meq ()
  priτVisAt-just subτ true  (just t′) meq ()
  priτVisAt-just subτ false (just t′) meq eqj = t′ , refl , meq , just-injective eqj

  -- invert a fired Pri-offer (RHS): `priVisAt … ≡ just u` ⇒ offer + residual
  priVisAt-just : {t : PTree E (ExtI E) R}
                  {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  (eqf′ : PTree.force t ≡ react v τc) (fb : FinBr t)
                  {at : AnyTypes E} {a : proj₁ at} {u : PTree E (ExtI E) R}
                  (dm : Bool) (dmeq : dominated? O v (at ∙ a) ≡ dm)
                  (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                → priVisAt O v eqf′ fb at a dm dmeq m meq ≡ just u
                → Σ[ t′ ∈ PTree E (ExtI E) R ] (dm ≡ false)
                    × Σ[ eva ∈ v at a ≡ just t′ ] (Pri O t′ (FinBr.next fb (sVis eqf′ eva)) ≡ u)
  priVisAt-just {t = t} eqf′ fb dm    dmeq nothing   meq ()
  priVisAt-just {t = t} eqf′ fb true  dmeq (just t′) meq ()
  priVisAt-just {t = t} eqf′ fb false dmeq (just t′) meq eqj = t′ , refl , meq , just-injective eqj

  -- fire a Pri-offer (RHS construct): dominated?=false + alive ⇒ `priVisAt ≡ just (Pri …)`
  priVisAt-fires : {t : PTree E (ExtI E) R}
                   {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                   (eqf′ : PTree.force t ≡ react v τc) (fb : FinBr t)
                   {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) R}
                   (dm : Bool) (dmeq : dominated? O v (at ∙ a) ≡ dm)
                   (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                 → dm ≡ false → m ≡ just t′
                 → Σ[ eva ∈ v at a ≡ just t′ ]
                     priVisAt O v eqf′ fb at a dm dmeq m meq ≡ just (Pri O t′ (FinBr.next fb (sVis eqf′ eva)))
  priVisAt-fires {t = t} eqf′ fb true  dmeq m         meq () mj
  priVisAt-fires {t = t} eqf′ fb false dmeq nothing   meq _  ()
  priVisAt-fires {t = t} eqf′ fb false dmeq (just t′) meq _  refl = meq , refl

  -- fire a priτ-offer (LHS construct)
  priτVisAt-fires : {t : PTree E (ExtI E) R}
                    {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    (subτ : ∀ {at a t′} → v at a ≡ just t′ → τ-Norm t′)
                    {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) R}
                    (dm : Bool) (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                  → dm ≡ false → m ≡ just t′
                  → Σ[ eva ∈ v at a ≡ just t′ ]
                      priτVisAt O v subτ at a dm m meq ≡ just (Priτ O t′ (subτ eva))
  priτVisAt-fires subτ true  m         meq () mj
  priτVisAt-fires subτ false nothing   meq _  ()
  priτVisAt-fires subτ false (just t′) meq _  refl = meq , refl

  -- the agreement relation: both sides are the two priorities of one τ-free node
  data AgreeR : PTree E (ExtI E) R → PTree E (ExtI E) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    agr : {t : PTree E (ExtI E) R} (τf : τ-Free t) (fb : FinBr t)
        → AgreeR (Priτ O t (free→cert τf)) (Pri O t fb)

  -- one-step simulations (bodies carry the corecursion ⇒ guarded, cf. ssim-trans)
  agree-∼  : {P Q : PTree E (ExtI E) R} → AgreeR P Q → P ∼ Q
  agree-∼ˢ : {P Q : PTree E (ExtI E) R} → AgreeR P Q → Q ∼ P
  afwd : {t : PTree E (ExtI E) R} (τf : τ-Free t) (fb : FinBr t)
       → SSimF (Sbisim R) (Priτ O t (free→cert τf)) (Pri O t fb)
  abwd : {t : PTree E (ExtI E) R} (τf : τ-Free t) (fb : FinBr t)
       → SSimF (Sbisim R) (Pri O t fb) (Priτ O t (free→cert τf))

  agree-∼  (agr τf fb) .Sbisim.fwd = afwd τf fb
  agree-∼  (agr τf fb) .Sbisim.bwd = abwd τf fb
  agree-∼ˢ (agr τf fb) .Sbisim.fwd = abwd τf fb
  agree-∼ˢ (agr τf fb) .Sbisim.bwd = afwd τf fb

  -- Priτ ⇒ Pri simulation
  afwd {t} τf fb .SSimF.on-ev step with free τf in feq
  ... | fret eqf =
        ret-∼ {P = Priτ O t (free→cert τf)} {Q = Pri O t fb} (cong (λ (ff : τ-FreeF t) → priτF O (free→certF ff)) feq) (fPri-ret {t = t} {fb = fb} eqf) .Sbisim.fwd .SSimF.on-ev step
  ... | fmenu {v = v} eqf stb subF with fPri-menu {t = t} eqf fb (mkStable {t = t} eqf stb) | step
  ...   | eqf′ , fq | sRet eqP =
          case trans (sym (cong (λ (ff : τ-FreeF t) → priτF O (free→certF ff)) feq)) eqP of λ ()
  ...   | eqf′ , fq | sVis {at = at} {a = a} eqP brP
          with priτVisAt-just {t = t} (λ br → free→cert (subF br)) (dominated? O v (at ∙ a)) (v at a) refl
                 (subst (λ V → V at a ≡ just _)
                    (sym (proj₁ (react-injective (trans (sym (cong (λ (ff : τ-FreeF t) → priτF O (free→certF ff)) feq)) eqP)))) brP)
  ...     | t′ , dmf , eva , refl with priVisAt-fires {t = t} eqf′ fb (dominated? O v (at ∙ a)) refl (v at a) refl dmf eva
  ...       | eva′ , brQ =
              Pri O t′ (FinBr.next fb (sVis eqf′ eva′)) , sVis fq brQ
                , agree-∼ (agr (subF eva) (FinBr.next fb (sVis eqf′ eva′)))
  afwd {t} τf fb .SSimF.on-tau step with free τf in feq
  ... | fret eqf =
        ret-∼ {P = Priτ O t (free→cert τf)} {Q = Pri O t fb} (cong (λ (ff : τ-FreeF t) → priτF O (free→certF ff)) feq) (fPri-ret {t = t} {fb = fb} eqf) .Sbisim.fwd .SSimF.on-tau step
  ... | fmenu eqf stb subF with step
  ...   | sSil eqP = case trans (sym (cong (λ (ff : τ-FreeF t) → priτF O (free→certF ff)) feq)) eqP of λ ()
  ...   | sTau {i = i} {a = a} eqP brP =
          case subst (λ T → T i a ≡ just _)
                 (sym (proj₂ (react-injective (trans (sym (cong (λ (ff : τ-FreeF t) → priτF O (free→certF ff)) feq)) eqP)))) brP
          of λ ()

  -- Pri ⇒ Priτ simulation
  abwd {t} τf fb .SSimF.on-ev step with free τf in feq
  ... | fret eqf =
        ret-∼ {P = Priτ O t (free→cert τf)} {Q = Pri O t fb} (cong (λ (ff : τ-FreeF t) → priτF O (free→certF ff)) feq) (fPri-ret {t = t} {fb = fb} eqf) .Sbisim.bwd .SSimF.on-ev step
  ... | fmenu {v = v} eqf stb subF with fPri-menu {t = t} eqf fb (mkStable {t = t} eqf stb) | step
  ...   | eqf′ , fq | sRet eqP = case trans (sym fq) eqP of λ ()
  ...   | eqf′ , fq | sVis {at = at} {a = a} eqP brP
          with priVisAt-just {t = t} eqf′ fb (dominated? O v (at ∙ a)) refl (v at a) refl
                 (subst (λ V → V at a ≡ just _)
                    (sym (proj₁ (react-injective (trans (sym fq) eqP)))) brP)
  ...     | t′ , dmf , eva , refl
            with priτVisAt-fires {t = t} (λ br → free→cert (subF br)) (dominated? O v (at ∙ a)) (v at a) refl dmf eva
  ...       | eva′ , brP′ =
              Priτ O t′ (free→cert (subF eva′)) , sVis (cong (λ (ff : τ-FreeF t) → priτF O (free→certF ff)) feq) brP′
                , agree-∼ˢ (agr (subF eva′) (FinBr.next fb (sVis eqf′ eva)))
  abwd {t} τf fb .SSimF.on-tau step with free τf in feq
  ... | fret eqf =
        ret-∼ {P = Priτ O t (free→cert τf)} {Q = Pri O t fb} (cong (λ (ff : τ-FreeF t) → priτF O (free→certF ff)) feq) (fPri-ret {t = t} {fb = fb} eqf) .Sbisim.bwd .SSimF.on-tau step
  ... | fmenu {v = v} eqf stb subF with fPri-menu {t = t} eqf fb (mkStable {t = t} eqf stb) | step
  ...   | eqf′ , fq | sSil eqP = case trans (sym fq) eqP of λ ()
  ...   | eqf′ , fq | sTau {i = i} {a = a} eqP brP =
          case subst (λ T → T i a ≡ just _)
                 (sym (proj₂ (react-injective (trans (sym fq) eqP)))) brP
          of λ ()

  -- MAIN: Priτ and Pri agree (∼) on the τ-free fragment (residuals via AgreeR)
  agree-τfree-∼ : {t : PTree E (ExtI E) R} (τf : τ-Free t) (fb : FinBr t)
                → Priτ O t (free→cert τf) ∼ Pri O t fb
  agree-τfree-∼ τf fb = agree-∼ (agr τf fb)
