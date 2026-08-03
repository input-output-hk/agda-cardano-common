{-# OPTIONS --guardedness #-}

-- FAILURE-SIMULATION congruence for SEQUENTIAL COMPOSITION (bind).
--
--   Bind-fsim  : BindDivSplit k₁ → (∀ r → FSim S (k₁ r) (k₂ r)) → FSim R P₁ P₂
--              → FSim S (P₁ >>= k₁) (P₂ >>= k₂)
-- with THREE side-condition-free corollaries:
--   bindNoτ-fsim : NoTauRoot k₁     -- every `k₁ r` is τ-less at its root
--                → (∀ r → FSim S (k₁ r) (k₂ r)) → FSim R P₁ P₂
--                → FSim S (P₁ >>= k₁) (P₂ >>= k₂)
--   bindκ-fsim   : (∀ r → Σ[ s ] force (k₁ r) ≡ ret s)     -- PURE continuation
--                → (∀ r → FSim S (k₁ r) (k₂ r)) → FSim R P₁ P₂
--                → FSim S (P₁ >>= k₁) (P₂ >>= k₂)
--   >>-fsim      : FSim R P₁ P₂ → FSim S Q₁ Q₂ → FSim S (P₁ >> Q₁) (P₂ >> Q₂)
--
-- ORIENTATION: in `FSim R t₁ t₂` the FIRST argument is the IMPLEMENTATION and the SECOND
-- the SPECIFICATION (`fsim→⊑FD : FSim R Q P → P ⊑FD Q`), so this says: if the spec
-- continuation failure-simulates the impl continuation at EVERY return value, and the spec
-- prefix failure-simulates the impl prefix, then the spec composition failure-simulates the
-- impl composition.  Composed with `fsim→⊑FD` it is a coinductive route to
-- `(P₂ >>= k₂) ⊑FD (P₁ >>= k₁)`.
--
-- WHY THE CONTINUATION HYPOTHESIS IS VALUE-INDEXED (`∀ r → FSim S (k₁ r) (k₂ r)`, not a
-- relation between the two sides' return values).  `WSimF.on-ev` matches a step of the impl
-- by a WEAK step of the spec CARRYING THE SAME LABEL, and a termination is the visible label
-- `√ r`.  So `FSim R P₁ P₂` already forces the two sides to agree on the returned value:
-- `fsim-reaches-ret` reads the spec's matching `√ r` step back as a τ*-run of `P₂` into a
-- state forcing to `ret r` — the SAME `r`.  A relation-indexed hypothesis would therefore be
-- unusable (nothing could ever discharge it beyond equality) as well as unnecessary; this is
-- also the shape the existing bisimulation congruence `CSP.Laws.Bisim.BindCong.>>=-cong`
-- uses (`∀ r → k r ≈ k′ r`).
--
-- The three fields.
--
--   fwd  : the `bwd`-free half of `CSP.Laws.Bisim.BindCong`'s `>>=-sim`, with `wbisim-trans`
--          replaced by `fsim-trans` and the `≈`-valued transport helpers replaced by
--          `fsim-force-≡` / `fsim-transport-τ*` / `═-force-transport`.  Case analysis is on
--          `force P₁`: at `sil`/`react` the step is the prefix's and the residual re-enters
--          `Bind-fsim`; at `ret r` the composite IS `k₁ r` (force-equal), the step is
--          delegated to `kk r`, and the spec composite first τ*-settles into `p₂ᵣ >>= k₂`
--          (`fsim-reaches-ret` + `bind-τ*`) before replaying the continuation's weak match
--          across the `force (p₂ᵣ >>= k₂) ≡ force (k₂ r)` boundary.
--
--   stab : the real work, and it needs NO side condition at all.  A stable `P₁ >>= k₁` is
--          classified by the new constructive `Bind-stable-normal` into
--          "P₁ itself is stable" or "P₁ has terminated (`force P₁ ≡ ret r`) and `k₁ r` is
--          stable" — a `sil` prefix is impossible.  In the first case the spec's PREFIX
--          settles by `pp .FSim.stab` and the run lifts by `bind-τ*`; in the second the
--          spec's prefix τ*-runs to its own `ret r` (`fsim-reaches-ret`) and the spec's
--          CONTINUATION settles by `kk r .FSim.stab`, its run transported across the
--          force-equality by `τ*-force-transport`.
--
--          THE √ ASYMMETRY, and it is visible in the TYPES: a `√` offered by `P₁` is
--          CONSUMED by the bind (it becomes the silent handover), and the two offer sets do
--          not even have the same type — `Event√ S` for the composite, `Event√ R` for the
--          prefix.  So `Bind-offer-elim-stable` returns an `evl` offer of the prefix TOGETHER
--          with the proof that the composite's offer was that `evl` (a composite `√` cannot
--          occur, since it needs a `ret` force and the composite is stable), and
--          `Bind-offer-intro-evl` goes back — the prefix's own `√` being the one offer that
--          never survives.  `Bind-offer-mono` composes the two around the operand's offer
--          inclusion.  In the handover case the composite's offers ARE the continuation's
--          offers, by force-equality (`offer-force-eq`).
--
--   div→ : the ONLY place a side condition is needed — see below.
--
-- SIDE CONDITION (`BindDivSplit k₁`, needed for `div→` ONLY).  Deciding whether an infinite
-- τ-chain of `P >>= k` stays inside `P` forever or `P` silently terminates and some `k r`
-- carries the divergence on is a König / infinite-pigeonhole step, exactly like the repo's
-- `□-Diverges→` / `Par-Diverges→` / `>>-Diverges→` / `loop-Diverges→` family.  The repo's
-- `>>-Diverges→` (`CSP.Laws.FD.SeqDistR`, certified from the single `dne` of
-- `CSP.Laws.ClassicalFromLEM`, Derivation 4) covers only the CONSTANT continuation `_>>_`,
-- so it cannot be reused for a general `k`.  Rather than introduce a new postulate this
-- module takes the split as an EXPLICIT HYPOTHESIS `BindDivSplit k₁` — a closed statement
-- (quantified over the prefix, with `k₁` fixed), so it threads through the corecursion
-- unchanged and never has to be re-established at residual states.  `fwd` and `stab` never
-- mention it.
--
-- The hypothesis is DISCHARGED, making the corollaries unconditional, in two cases:
--   • a τ-FREE-ROOT continuation (`NoTauRoot k`: no `k r` can take a τ-step, i.e. each forces
--     to a `ret` or to a STABLE `react`): CONSTRUCTIVELY, by `bind-noτ-split` /
--     `Diverges-noτ-bind→` — the handover node then offers no τ at all, so the τ-chain can
--     never cross it and the second disjunct cannot arise.  This covers the node
--     specifications of interest, `consume … >>= λ b → produce … b` with `produce b` starting
--     from a visible offer, and (via `pure→NoTauRoot`) the iterate / loop continuations
--     `κ a = Ret (inj₁ a)`.  What it does NOT cover is a continuation that may itself begin
--     with a τ (an internal choice or a divergence at its very root) — there the König
--     decision is genuinely classical and the hypothesis must be supplied.
--   • a CONSTANT continuation (`_>>_`): from the pre-existing repo-certified `>>-Diverges→`
--     (`>>-split`), the same reliance on the same certified König family that
--     `CSP.Laws.FSim.ParCong.Par-fsim-div→` and `CSP.Laws.Bisim.DRCongruence.cong-Par⊤-div→`
--     have on `Par-Diverges→`.
--
-- This module declares NO postulate, no NON_TERMINATING, no sized type and no hole.
-- `Bind-fsim`, `bindNoτ-fsim` and `bindκ-fsim` are classical-ingredient-free (the König step
-- is a hypothesis, resp. constructively discharged); only `>>-fsim` uses the one pre-existing
-- certified postulate named above.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; [])
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Function using (case_of_)

open import Process_Trees

module CSP.Laws.FSim.BindCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS        {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.Refusals   {E = E} {I = ExtI E} using (Offers)
open import Semantics.DRBisim    {E = E} {I = ExtI E} using (Diverges)
open import Semantics.FailureSim {E = E} {I = ExtI E}
  using (FSim; fsim-refl; fsim-trans; fsim-τ*-sim)
open import CSP.Laws.Bisim.IterCong E-≟ using (ret-no-τ; sil-no-ev; sil-τ-inv; react-τ-inv)
open import CSP.Laws.Bisim.LoopCong E-≟
  using (fBind-ret; fBind-sil; fBind-react; bindV-elim; bindT-elim; bind-ev; bind-τ*)
open import CSP.Laws.FD.BindFD E-≟
  using (─►-force-cong; stable-force-eq; Diverges-force-eq; Diverges->>=)
open import CSP.Laws.FD.ParallelRefusals E-≟
  using (stable→react; mk-stable)
open import CSP.Laws.FD.SeqDistR E-≟
  using (>>-Diverges→; _⟹ₚ⟨_⟩_; ⟹ₚ-refl; ⟹ₚ-τ)

private
  variable
    ℓr ℓs : Level
    R : Set ℓr
    S : Set ℓs

-------------------------------------------------------------------------------------
-- GENERIC force-boundary transport.  `>>=` splices at a `ret`: `force (P >>= k)` is
-- LITERALLY `force (k r)` there, with no τ and no √ in between, so every proof obligation
-- has to be carried across a bare `force p ≡ force q` boundary.  These are the FSim
-- analogues of `CSP.Laws.Bisim.BindCong`'s `≈`-valued `force-≡→≈` / `weak-transport-*`.
-------------------------------------------------------------------------------------

-- an offer depends on its tree only through `force` (a step reads its source's `force`)
offer-force-eq : {p q : PTree E (ExtI E) S} {e : Event√ S}
               → PTree.force p ≡ PTree.force q → Offers q e → Offers p e
offer-force-eq eq (t , step) = t , ─►-force-cong (sym eq) step

-- force-equal trees are one-way failure-similar (in BOTH directions, but one is all we
-- ever need at a time): every step, every stability witness and every divergence of the
-- one is literally one of the other.
fsim-force-≡ : {p q : PTree E (ExtI E) S}
             → PTree.force p ≡ PTree.force q → FSim S p q
fsim-force-≡ eq .FSim.fwd .WSimF.on-ev  step =
  _ , wev τ*-refl (─►-force-cong eq step) τ*-refl , fsim-refl _
fsim-force-≡ eq .FSim.fwd .WSimF.on-tau step =
  _ , wτ (τ*-step (─►-force-cong eq step) τ*-refl) , fsim-refl _
fsim-force-≡ {p = p} {q = q} eq .FSim.stab st =
  q , τ*-refl , stable-force-eq {p = q} {q = p} (sym eq) st
    , λ _ off → offer-force-eq eq off
fsim-force-≡ eq .FSim.div→ d = Diverges-force-eq (sym eq) d

-- replay a τ*-run across a force-equality.  A non-empty run transports its first step and
-- keeps its endpoint; the EMPTY run has to move its endpoint from `q` to `p`, which is why
-- the result is only force-equal (not equal) to the original endpoint.
τ*-force-transport : {p q u : PTree E (ExtI E) S}
                   → PTree.force p ≡ PTree.force q → q ─[τ*]─► u
                   → Σ[ u′ ∈ PTree E (ExtI E) S ]
                       ((p ─[τ*]─► u′) × (PTree.force u′ ≡ PTree.force u))
τ*-force-transport {p = p} eq τ*-refl           = p , τ*-refl , eq
τ*-force-transport         eq (τ*-step st rest) =
  _ , τ*-step (─►-force-cong (sym eq) st) rest , refl

-- the same, packaged with an FSim between the original and the transported endpoint (so a
-- residual `FSim … u` composes to a residual `FSim … u′` by `fsim-trans`)
fsim-transport-τ* : {p q u : PTree E (ExtI E) S}
                  → PTree.force p ≡ PTree.force q → q ─[τ*]─► u
                  → Σ[ u′ ∈ PTree E (ExtI E) S ] ((p ─[τ*]─► u′) × FSim S u u′)
fsim-transport-τ* eq run with τ*-force-transport eq run
... | u′ , run′ , equ = u′ , run′ , fsim-force-≡ (sym equ)

-- replay a WEAK VISIBLE run across a force-equality.  Here the endpoint never moves: the
-- run contains a visible step, so either its leading τ*-run is non-empty (transport its
-- first step) or the visible step itself is at the boundary (transport that).
═-force-transport : {p q u : PTree E (ExtI E) S} {l : Event√ S}
                  → PTree.force p ≡ PTree.force q → q ═[ ev l ]═► u → p ═[ ev l ]═► u
═-force-transport eq (wev τ*-refl           evst post) =
  wev τ*-refl (─►-force-cong (sym eq) evst) post
═-force-transport eq (wev (τ*-step st rest) evst post) =
  wev (τ*-step (─►-force-cong (sym eq) st) rest) evst post

-- prepend a τ*-run to a weak step (the `═-prepend-τ*` of the bisim BindCong, FSim-free)
═-prepend-τ* : {p q u : PTree E (ExtI E) S} {l : Label S}
             → p ─[τ*]─► q → q ═[ l ]═► u → p ═[ l ]═► u
═-prepend-τ* pre (wτ  q→u)             = wτ  (τ*-trans pre q→u)
═-prepend-τ* pre (wev q→q′ evst q″→u) = wev (τ*-trans pre q→q′) evst q″→u

-- a finite τ-chain in front of a divergence is still a divergence (a local copy of
-- `CSP.Laws.FD.InterruptFD.τ*-Diverges`, which is not imported: that module is 1400 lines
-- of interrupt-specific FD theory and pulling it in for four lines would cost far more
-- typechecking time than it saves)
div-prepend-τ* : {t u : PTree E (ExtI E) S} → t ─[τ*]─► u → Diverges u → Diverges t
div-prepend-τ* τ*-refl           d = d
div-prepend-τ* (τ*-step st rest) d .Diverges.next = _
div-prepend-τ* (τ*-step st rest) d .Diverges.step = st
div-prepend-τ* (τ*-step st rest) d .Diverges.rest = div-prepend-τ* rest d

-- the FSim analogue of `LoopCong.≈-reaches-ret`: the spec answers the impl's `√ r` step
-- with a weak `√ r` step, whose visible move can only be `sRet`, i.e. the spec silently
-- reaches a state that forces to `ret r` — the SAME `r`.
fsim-reaches-ret : {P₁ P₂ : PTree E (ExtI E) R} {r : R}
                 → FSim R P₁ P₂ → PTree.force P₁ ≡ ret r
                 → Σ[ p′ ∈ PTree E (ExtI E) R ]
                     ((P₂ ─[τ*]─► p′) × (PTree.force p′ ≡ ret r))
fsim-reaches-ret sim eqP with sim .FSim.fwd .WSimF.on-ev (sRet eqP)
... | _ , wev q→p′ (sRet fp′) _ , _ = _ , q→p′ , fp′

-------------------------------------------------------------------------------------
-- WHEN IS `P >>= k` STABLE?  Read off `force (P >>= k)`: a `ret` prefix splices to
-- `force (k r)`, a `sil` prefix stays a `sil` (never stable), and a `react` prefix keeps
-- its τ-branch map wrapped by `bindT` (which is `nothing` exactly where the prefix's is).
-------------------------------------------------------------------------------------

-- `bindT` is `nothing` wherever the underlying `viewT` is (offer-map intro)
bindT-nothing : (k : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
                {i : AnyTypes (ExtI E)} {a : proj₁ i}
              → viewT nP i a ≡ nothing → bindT k nP i a ≡ nothing
bindT-nothing k nP {i} {a} eq with viewT nP i a
... | nothing = refl
... | just _  = case eq of λ ()

-- …and only there (offer-map elim)
bindT-nothing-inv : (k : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
                    {i : AnyTypes (ExtI E)} {a : proj₁ i}
                  → bindT k nP i a ≡ nothing → viewT nP i a ≡ nothing
bindT-nothing-inv k nP {i} {a} eq with viewT nP i a
... | nothing = refl
... | just _  = case eq of λ ()

-- a state whose `force` is a `sil` is not stable.  (The `sil` companion of
-- `ParallelRefusals.stable-not-ret`; proved here rather than imported from
-- `Semantics.DRImpliesFD`, whose classical `¬-divergent→normal` postulate this suite
-- deliberately stays clear of.)
stable-not-sil : {t c : PTree E (ExtI E) S} → PTree.force t ≡ sil c → isStable t → ⊥
stable-not-sil {t = t} eqf st with stable→react {t = t} st
... | _ , _ , eqr , _ = sil≢react (trans (sym eqf) eqr)

-- a stable composite with a `react` prefix forces that prefix's τ-branch map to be
-- everywhere `nothing` — i.e. the prefix is itself stable
bind-stable-τc : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                 {v  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) R))}
                 {τc : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) R))}
               → PTree.force P ≡ react v τc → isStable (P >>= k)
               → ∀ i a → τc i a ≡ nothing
bind-stable-τc P k {v} {τc} eqP st i a with stable→react {t = P >>= k} st
... | v′ , τc′ , eqB , h =
      bindT-nothing-inv k (react v τc)
        (subst (λ g → g i a ≡ nothing)
               (sym (proj₂ (react-injective (trans (sym (fBind-react k P eqP)) eqB))))
               (h i a))

-- STABILITY NORMAL FORM: a stable `P >>= k` is either still in its prefix (P stable) or
-- has handed over (P terminated at `r` and `k r` is stable).  Constructive.
--
-- The case analysis is on a NAMED node argument with its force-equation supplied, not on
-- `with PTree.force P in eqP`: the conclusion mentions `PTree.force P`, so a `with` would
-- abstract it there and hand back a vacuous `ret r ≡ ret r`.
Bind-stable-normal-node : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                          (nP : NodeKind E (ExtI E) R)
                        → PTree.force P ≡ nP → isStable (P >>= k)
                        → isStable P
                        ⊎ (Σ[ r ∈ R ] ((PTree.force P ≡ ret r) × isStable (k r)))
Bind-stable-normal-node P k (ret r)      eqP st =
  inj₂ (r , eqP , stable-force-eq {p = k r} {q = P >>= k} (sym (fBind-ret k P eqP)) st)
Bind-stable-normal-node P k (sil c)      eqP st =
  ⊥-elim (stable-not-sil {t = P >>= k} {c = c >>= k} (fBind-sil k P eqP) st)
Bind-stable-normal-node P k (react v τc) eqP st =
  inj₁ (mk-stable {t = P} eqP (bind-stable-τc P k eqP st))

-- the classification, at the prefix's actual node
Bind-stable-normal : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                   → isStable (P >>= k)
                   → isStable P
                   ⊎ (Σ[ r ∈ R ] ((PTree.force P ≡ ret r) × isStable (k r)))
Bind-stable-normal P k st = Bind-stable-normal-node P k (PTree.force P) refl st

-- STABILITY INTRO, prefix case: a stable prefix makes the whole composite stable (`bindT`
-- inherits "everywhere nothing" from the prefix's own τ-branch map)
Bind-stable-P : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
              → isStable P → isStable (P >>= k)
Bind-stable-P P k st with stable→react {t = P} st
... | v , τc , eqP , h =
      mk-stable {t = P >>= k} (fBind-react k P eqP)
                (λ i a → bindT-nothing k (react v τc) (h i a))

-- STABILITY INTRO, handover case: at a `ret` the composite IS the continuation
Bind-stable-ret : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S) {r : R}
                → PTree.force P ≡ ret r → isStable (k r) → isStable (P >>= k)
Bind-stable-ret P k {r} eqP st =
  stable-force-eq {p = P >>= k} {q = k r} (fBind-ret k P eqP) st

-------------------------------------------------------------------------------------
-- OFFER DECOMPOSITION for `stab`.  THE √ ASYMMETRY IS VISIBLE IN THE TYPES: the composite's
-- offers live in `Event√ S`, the prefix's in `Event√ R`, and the bind CONSUMES the prefix's
-- `√` (it becomes the silent handover).  So the two offer sets can only ever agree on the
-- carrier-independent `evl` events — which is enough, because with a stable prefix a `√`
-- offer is impossible on either side (a `√` step is `sRet`, needing a `ret` force).
-------------------------------------------------------------------------------------

-- OFFER ELIM: every offer of a still-in-prefix composite is an `evl` offer of the prefix
Bind-offer-elim-react : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                        {v  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) R))}
                        {τc : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) R))}
                      → PTree.force P ≡ react v τc
                      → ∀ (e : Event√ S) → Offers (P >>= k) e
                      → Σ[ l ∈ Event ] ((e ≡ evl l) × Offers P (evl l))
Bind-offer-elim-react P k eqP e (_ , sRet eqf) =
  ⊥-elim (case trans (sym (fBind-react k P eqP)) eqf of λ ())
Bind-offer-elim-react P k {v} {τc} eqP e (_ , sVis {at = at} {a = a} eqf br)
  with bindV-elim k (react v τc)
         (subst (λ g → g at a ≡ just _)
                (sym (proj₁ (react-injective (trans (sym (fBind-react k P eqP)) eqf))))
                br)
... | t″ , vv , refl =
      evLabel (proj₁ at) (proj₂ at) a , refl , (t″ , sVis eqP vv)

-- the same for a STABLE prefix (a stable state forces to a `react` node)
Bind-offer-elim-stable : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                       → isStable P
                       → ∀ (e : Event√ S) → Offers (P >>= k) e
                       → Σ[ l ∈ Event ] ((e ≡ evl l) × Offers P (evl l))
Bind-offer-elim-stable P k st e off with stable→react {t = P} st
... | _ , _ , eqP , _ = Bind-offer-elim-react P k eqP e off

-- OFFER INTRO: an `evl` offer of the prefix is an offer of the composite (unconditional —
-- the prefix's `√` is the one offer that does NOT survive, and `evl` excludes it)
Bind-offer-intro-evl : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                     → ∀ (l : Event) → Offers P (evl l) → Offers (P >>= k) (evl l)
Bind-offer-intro-evl P k l (t , sVis eqf br) = t >>= k , bind-ev k P (sVis eqf br)

-- OFFER MONOTONICITY: prefix-wise offer inclusion composes to composite offer inclusion
Bind-offer-mono : (k₁ k₂ : R → PTree E (ExtI E) S)
                  (P₁ P₂ : PTree E (ExtI E) R)
                → isStable P₂
                → (∀ (e : Event√ R) → Offers P₂ e → Offers P₁ e)
                → ∀ (e : Event√ S) → Offers (P₂ >>= k₂) e → Offers (P₁ >>= k₁) e
Bind-offer-mono k₁ k₂ P₁ P₂ stP₂ incl e off
  with Bind-offer-elim-stable P₂ k₂ stP₂ e off
... | l , refl , o = Bind-offer-intro-evl P₁ k₁ l (incl (evl l) o)

-------------------------------------------------------------------------------------
-- THE `stab` FIELD, one named lemma per `Bind-stable-normal` leaf.  NO side condition.
-------------------------------------------------------------------------------------

-- PREFIX STILL RUNNING: settle the spec's prefix with its own `FSim.stab` and lift that
-- silent run through `>>= k₂`; offers compose prefix-wise by the two offer lemmas.
Bind-fsim-stab-P : (k₁ k₂ : R → PTree E (ExtI E) S)
                   {P₁ P₂ : PTree E (ExtI E) R}
                 → FSim R P₁ P₂ → isStable P₁
                 → Σ[ M ∈ PTree E (ExtI E) S ]
                     ( (P₂ >>= k₂) ─[τ*]─► M × isStable M
                     × (∀ (e : Event√ S) → Offers M e → Offers (P₁ >>= k₁) e) )
Bind-fsim-stab-P k₁ k₂ {P₁} {P₂} pp stP with pp .FSim.stab stP
... | P₂* , rP , stP* , inclP =
      P₂* >>= k₂
    , bind-τ* k₂ rP
    , Bind-stable-P P₂* k₂ stP*
    , Bind-offer-mono k₁ k₂ P₁ P₂* stP* inclP

-- HANDOVER: the impl's prefix has terminated at `r`, so the impl composite IS `k₁ r`.  The
-- spec composite first silently follows its prefix to its own `ret r` (`fsim-reaches-ret`,
-- lifted by `bind-τ*`), and then settles the CONTINUATION with `kk r .FSim.stab`, whose run
-- is replayed across the splice boundary by `τ*-force-transport`.
Bind-fsim-stab-ret : (k₁ k₂ : R → PTree E (ExtI E) S)
                     {P₁ P₂ : PTree E (ExtI E) R} {r : R}
                   → FSim R P₁ P₂ → (∀ r′ → FSim S (k₁ r′) (k₂ r′))
                   → PTree.force P₁ ≡ ret r → isStable (k₁ r)
                   → Σ[ M ∈ PTree E (ExtI E) S ]
                       ( (P₂ >>= k₂) ─[τ*]─► M × isStable M
                       × (∀ (e : Event√ S) → Offers M e → Offers (P₁ >>= k₁) e) )
Bind-fsim-stab-ret k₁ k₂ {P₁} {P₂} {r} pp kk eqP stk
  with fsim-reaches-ret pp eqP | kk r .FSim.stab stk
... | p₂ᵣ , run₂ , eqr₂ | K* , runK , stK* , inclK
      with τ*-force-transport (fBind-ret k₂ p₂ᵣ eqr₂) runK
...     | M , runM , eqM =
          M
        , τ*-trans (bind-τ* k₂ run₂) runM
        , stable-force-eq {p = M} {q = K*} eqM stK*
        , λ e off → offer-force-eq (fBind-ret k₁ P₁ eqP)
                      (inclK e (offer-force-eq (sym eqM) off))

-- the `stab` field itself: classify the stable impl composite, apply the matching leaf
Bind-fsim-stab : (k₁ k₂ : R → PTree E (ExtI E) S)
                 {P₁ P₂ : PTree E (ExtI E) R}
               → FSim R P₁ P₂ → (∀ r → FSim S (k₁ r) (k₂ r))
               → isStable (P₁ >>= k₁)
               → Σ[ M ∈ PTree E (ExtI E) S ]
                   ( (P₂ >>= k₂) ─[τ*]─► M × isStable M
                   × (∀ (e : Event√ S) → Offers M e → Offers (P₁ >>= k₁) e) )
Bind-fsim-stab k₁ k₂ {P₁} {P₂} pp kk st with Bind-stable-normal P₁ k₁ st
... | inj₁ stP              = Bind-fsim-stab-P   k₁ k₂ pp stP
... | inj₂ (r , eqP , stk)  = Bind-fsim-stab-ret k₁ k₂ pp kk eqP stk

-------------------------------------------------------------------------------------
-- THE `div→` FIELD.  The ONE place a side condition is needed: the bind König step.
-------------------------------------------------------------------------------------

-- The BIND KÖNIG STEP for a FIXED continuation, as an explicit hypothesis: an infinite
-- τ-chain of `P >>= k` either stays inside `P` forever, or `P` silently terminates at some
-- `r` and `k r` diverges.  Classical (see the header); `>>-split` discharges the constant
-- continuation instance from the repo's certified `>>-Diverges→`.
BindDivSplit : ∀ {ℓr′ ℓs′} {R : Set ℓr′} {S : Set ℓs′}
             → (k : R → PTree E (ExtI E) S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr′ ⊔ ℓs′)
BindDivSplit {R = R} k =
    ∀ (P : PTree E (ExtI E) R)
  → Diverges (P >>= k)
  → Diverges P
  ⊎ (Σ[ P′ ∈ PTree E (ExtI E) R ] Σ[ r ∈ R ]
       ((P ─[τ*]─► P′) × (PTree.force P′ ≡ ret r) × Diverges (k r)))

-- A continuation is τ-FREE AT THE ROOT when no `k r` can take a τ-step — i.e. every `k r`
-- forces to a `ret` (a PURE continuation) or to a STABLE `react` (an immediate offer, e.g.
-- a prefixed process).  This is exactly what makes the König decision TRIVIAL: the handover
-- node of `P >>= k` inherits `force (k r)`, so it offers no τ, so an infinite τ-chain of
-- `P >>= k` can never cross the handover and must stay inside the prefix.
NoTauRoot : ∀ {ℓr′ ℓs′} {R : Set ℓr′} {S : Set ℓs′}
          → (k : R → PTree E (ExtI E) S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr′ ⊔ ℓs′)
NoTauRoot {R = R} {S = S} k = ∀ (r : R) {u : PTree E (ExtI E) S} → ¬ ((k r) ─[ τ ]─► u)

-- a stable state has no τ-step (local 4-line copy: the existing `stable-no-τ` lives in
-- `CSP.Priority.Laws.Cong`, and the priority stack is no dependency for a bind law)
stable-no-τ : {t u : PTree E (ExtI E) S} → isStable t → t ─[ τ ]─► u → ⊥
stable-no-τ {t = t} st step with stable→react {t = t} st
... | v , τc , eqP , h with react-τ-inv eqP step
...   | i , a , br = case trans (sym br) (h i a) of λ ()

-- a PURE (`ret`-forcing) continuation is τ-free at the root
pure→NoTauRoot : (k : R → PTree E (ExtI E) S)
               → (∀ r → Σ[ s ∈ S ] (PTree.force (k r) ≡ ret s)) → NoTauRoot k
pure→NoTauRoot k pure r step = ret-no-τ (proj₂ (pure r)) step

-- a STABLE continuation is τ-free at the root
stable→NoTauRoot : (k : R → PTree E (ExtI E) S)
                 → (∀ r → isStable (k r)) → NoTauRoot k
stable→NoTauRoot k st r step = stable-no-τ (st r) step

-- τ-INVERSION for such a continuation: every τ of `P >>= k` is a τ of `P`, with the target
-- still in bind form.  (Node argument + force-equation rather than
-- `with PTree.force P in eqP`, so that nothing in the context is silently abstracted.)
bind-noτ-τ-elim-node : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                     → NoTauRoot k
                     → (nP : NodeKind E (ExtI E) R) → PTree.force P ≡ nP
                     → {t : PTree E (ExtI E) S} → (P >>= k) ─[ τ ]─► t
                     → Σ[ P′ ∈ PTree E (ExtI E) R ]
                         ((P ─[ τ ]─► P′) × (t ≡ P′ >>= k))
bind-noτ-τ-elim-node P k noτ (ret r) eqP step =
  ⊥-elim (noτ r (─►-force-cong (fBind-ret k P eqP) step))
bind-noτ-τ-elim-node P k noτ (sil c) eqP step =
  c , sSil eqP , sil-τ-inv (fBind-sil k P eqP) step
bind-noτ-τ-elim-node P k noτ (react v τc) eqP step
  with react-τ-inv (fBind-react k P eqP) step
... | i , a , br with bindT-elim k (react v τc) br
...   | t′ , vτ , teq = t′ , sTau eqP vτ , teq

-- the same at the prefix's actual node
bind-noτ-τ-elim : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                → NoTauRoot k
                → {t : PTree E (ExtI E) S} → (P >>= k) ─[ τ ]─► t
                → Σ[ P′ ∈ PTree E (ExtI E) R ]
                    ((P ─[ τ ]─► P′) × (t ≡ P′ >>= k))
bind-noτ-τ-elim P k noτ step =
  bind-noτ-τ-elim-node P k noτ (PTree.force P) refl step

-- CONSTRUCTIVE divergence peel: the τ-chain can never leave the prefix, so it projects
-- step-by-step onto an infinite τ-chain of the prefix.  Corecursion guarded under the
-- `Diverges` fields; the inversion is repeated in each field (rather than `with`-bound once)
-- so the recursive call sits syntactically under the constructor — the shape of
-- `CSP.Laws.FD.IterateMonoFD.bind-loopk-Diverges→`.
Diverges-noτ-bind→ : (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                   → NoTauRoot k → Diverges (P >>= k) → Diverges P
Diverges-noτ-bind→ P k noτ d .Diverges.next =
  proj₁ (bind-noτ-τ-elim P k noτ (d .Diverges.step))
Diverges-noτ-bind→ P k noτ d .Diverges.step =
  proj₁ (proj₂ (bind-noτ-τ-elim P k noτ (d .Diverges.step)))
Diverges-noτ-bind→ P k noτ d .Diverges.rest =
  Diverges-noτ-bind→ (proj₁ (bind-noτ-τ-elim P k noτ (d .Diverges.step))) k noτ
    (subst Diverges (proj₂ (proj₂ (bind-noτ-τ-elim P k noτ (d .Diverges.step))))
           (d .Diverges.rest))

-- τ-FREE-ROOT instance of the König hypothesis — CONSTRUCTIVE, no classical step: the
-- second disjunct simply cannot arise.
bind-noτ-split : (k : R → PTree E (ExtI E) S) → NoTauRoot k → BindDivSplit k
bind-noτ-split k noτ P d = inj₁ (Diverges-noτ-bind→ P k noτ d)

-- divergence transfer: split the impl composite's livelock, push the guilty half through
-- its own `div→`, and re-lift (prefix half by `Diverges->>=`; handover half by lifting the
-- two silent runs with `bind-τ*` and crossing the splice with `Diverges-force-eq`).
Bind-fsim-div→ : (k₁ k₂ : R → PTree E (ExtI E) S)
               → BindDivSplit k₁ → (∀ r → FSim S (k₁ r) (k₂ r))
               → {P₁ P₂ : PTree E (ExtI E) R} → FSim R P₁ P₂
               → Diverges (P₁ >>= k₁) → Diverges (P₂ >>= k₂)
Bind-fsim-div→ k₁ k₂ kön kk {P₁} {P₂} pp d with kön P₁ d
... | inj₁ dP = Diverges->>= k₂ (pp .FSim.div→ dP)
... | inj₂ (P₁′ , r , run , eqr , dk) with fsim-τ*-sim run pp
...   | P₂′ , run₂ , rel with fsim-reaches-ret rel eqr
...     | p₂ᵣ , run₃ , eqr₂ =
          div-prepend-τ* (τ*-trans (bind-τ* k₂ run₂) (bind-τ* k₂ run₃))
                         (Diverges-force-eq (fBind-ret k₂ p₂ᵣ eqr₂)
                                            (kk r .FSim.div→ dk))

-------------------------------------------------------------------------------------
-- THE CONGRUENCE.  Forward declarations (no old-style mutual block): the corecursive
-- `Bind-fsim` residuals sit under the `WSimF` Σ-results of `f-sim-Bind`, exactly the
-- guardedness discipline of `CSP.Laws.Bisim.BindCong.>>=-sim`.  Only the PREFIX is ever
-- forced (`with PTree.force P₁`) — never a composite.
-------------------------------------------------------------------------------------

-- HEADLINE: `>>=` is an FSim congruence (spec prefix/continuation failure-simulate the
-- impl prefix/continuation), modulo the bind König step for the impl continuation
Bind-fsim : (k₁ k₂ : R → PTree E (ExtI E) S)
          → BindDivSplit k₁ → (∀ r → FSim S (k₁ r) (k₂ r))
          → {P₁ P₂ : PTree E (ExtI E) R} → FSim R P₁ P₂
          → FSim S (P₁ >>= k₁) (P₂ >>= k₂)

-- the forward-simulation half: invert an impl composite step by cases on `force P₁`
f-sim-Bind : (k₁ k₂ : R → PTree E (ExtI E) S)
           → BindDivSplit k₁ → (∀ r → FSim S (k₁ r) (k₂ r))
           → {P₁ P₂ : PTree E (ExtI E) R} → FSim R P₁ P₂
           → WSimF (FSim S) (P₁ >>= k₁) (P₂ >>= k₂)

-- τ steps
f-sim-Bind k₁ k₂ kön kk {P₁} {P₂} pp .WSimF.on-tau step with PTree.force P₁ in eqP
-- HANDOVER: the composite is force-equal to `k₁ r`, so the τ is the continuation's
... | ret r
      with kk r .FSim.fwd .WSimF.on-tau (─►-force-cong (fBind-ret k₁ P₁ eqP) step)
         | fsim-reaches-ret pp eqP
...     | u′ , wτ run , rel | p₂ᵣ , run₂ , eqr₂
          with fsim-transport-τ* (fBind-ret k₂ p₂ᵣ eqr₂) run
...         | u″ , run″ , rel′ =
              u″ , wτ (τ*-trans (bind-τ* k₂ run₂) run″) , fsim-trans rel rel′
-- a silent step of the prefix
f-sim-Bind k₁ k₂ kön kk {P₁} {P₂} pp .WSimF.on-tau step | sil c
  with sil-τ-inv (fBind-sil k₁ P₁ eqP) step | pp .FSim.fwd .WSimF.on-tau (sSil eqP)
...   | refl | c₂ , wτ run , relc =
        c₂ >>= k₂ , wτ (bind-τ* k₂ run) , Bind-fsim k₁ k₂ kön kk relc
-- an internal (τ-branch) step of the prefix
f-sim-Bind k₁ k₂ kön kk {P₁} {P₂} pp .WSimF.on-tau step | react v τc
  with react-τ-inv (fBind-react k₁ P₁ eqP) step
...   | i , a , br with bindT-elim k₁ (react v τc) br
...     | t″ , vτ , refl with pp .FSim.fwd .WSimF.on-tau (sTau eqP vτ)
...       | t₂ , wτ run , rel =
            t₂ >>= k₂ , wτ (bind-τ* k₂ run) , Bind-fsim k₁ k₂ kön kk rel

-- visible steps (including √)
f-sim-Bind k₁ k₂ kön kk {P₁} {P₂} pp .WSimF.on-ev step with PTree.force P₁ in eqP
-- a `sil` prefix offers nothing visible
... | sil c = ⊥-elim (sil-no-ev (fBind-sil k₁ P₁ eqP) step)
-- HANDOVER: the visible step (a real event OR the composite's √) is the continuation's
... | ret r
      with kk r .FSim.fwd .WSimF.on-ev (─►-force-cong (fBind-ret k₁ P₁ eqP) step)
         | fsim-reaches-ret pp eqP
...     | u′ , wk , rel | p₂ᵣ , run₂ , eqr₂ =
          u′
        , ═-prepend-τ* (bind-τ* k₂ run₂) (═-force-transport (fBind-ret k₂ p₂ᵣ eqr₂) wk)
        , rel
-- a visible offer of the prefix (a √ is impossible: `force (P₁ >>= k₁)` is a `react`)
f-sim-Bind k₁ k₂ kön kk {P₁} {P₂} pp .WSimF.on-ev step | react v τc with step
... | sRet eqf = ⊥-elim (case trans (sym (fBind-react k₁ P₁ eqP)) eqf of λ ())
... | sVis {at = at} {a = a} eqf br
      with bindV-elim k₁ (react v τc)
             (subst (λ g → g at a ≡ just _)
                    (sym (proj₁ (react-injective
                                  (trans (sym (fBind-react k₁ P₁ eqP)) eqf))))
                    br)
...   | t″ , vv , refl with pp .FSim.fwd .WSimF.on-ev (sVis eqP vv)
...     | t₂ , wev pre evst post , rel =
          t₂ >>= k₂
        , wev (bind-τ* k₂ pre) (bind-ev k₂ _ evst) (bind-τ* k₂ post)
        , Bind-fsim k₁ k₂ kön kk rel

Bind-fsim k₁ k₂ kön kk pp .FSim.fwd      = f-sim-Bind     k₁ k₂ kön kk pp
Bind-fsim k₁ k₂ kön kk pp .FSim.stab st  = Bind-fsim-stab  k₁ k₂ pp kk st
Bind-fsim k₁ k₂ kön kk pp .FSim.div→  d  = Bind-fsim-div→  k₁ k₂ kön kk pp d

-------------------------------------------------------------------------------------
-- THE `_>>_` COROLLARY: for a CONSTANT continuation the König hypothesis is discharged
-- from the pre-existing, `dne`-certified `>>-Diverges→`, so this congruence needs no
-- side condition at all.
-------------------------------------------------------------------------------------

-- a √-free empty-trace weak reach is just a τ*-run
⟹ₚ[]→τ* : {P P′ : PTree E (ExtI E) R} → P ⟹ₚ⟨ [] ⟩ P′ → P ─[τ*]─► P′
⟹ₚ[]→τ* ⟹ₚ-refl        = τ*-refl
⟹ₚ[]→τ* (⟹ₚ-τ st rest) = τ*-step st (⟹ₚ[]→τ* rest)

-- the constant-continuation instance of the bind König step
>>-split : (X : PTree E (ExtI E) S) → BindDivSplit {R = R} (λ _ → X)
>>-split X P d with >>-Diverges→ {P′ = P} {X = X} d
... | inj₁ dP                            = inj₁ dP
... | inj₂ (P″ , r , reach , eqr , dX) =
      inj₂ (P″ , r , ⟹ₚ[]→τ* reach , eqr , dX)

-- `>>=` with a τ-FREE-ROOT continuation (every `k₁ r` forces to a `ret` or to a stable
-- `react`) is an FSim congruence with NO side condition.  This is the case that covers the
-- node specifications of interest — `consume … >>= λ b → produce … b`, where `produce b`
-- starts with a visible offer — as well as the iterate / loop continuations.
bindNoτ-fsim : (k₁ k₂ : R → PTree E (ExtI E) S)
             → NoTauRoot k₁
             → (∀ r → FSim S (k₁ r) (k₂ r))
             → {P₁ P₂ : PTree E (ExtI E) R} → FSim R P₁ P₂
             → FSim S (P₁ >>= k₁) (P₂ >>= k₂)
bindNoτ-fsim k₁ k₂ noτ kk pp = Bind-fsim k₁ k₂ (bind-noτ-split k₁ noτ) kk pp

-- the PURE-continuation specialisation — the FSim analogue of
-- `CSP.Laws.Bisim.LoopCong.bindκ-cong`, and the shape the iterate / loop congruences
-- consume (their continuation is `λ a → Ret (inj₁ a)`).
bindκ-fsim : (k₁ k₂ : R → PTree E (ExtI E) S)
           → (∀ r → Σ[ s ∈ S ] (PTree.force (k₁ r) ≡ ret s))
           → (∀ r → FSim S (k₁ r) (k₂ r))
           → {P₁ P₂ : PTree E (ExtI E) R} → FSim R P₁ P₂
           → FSim S (P₁ >>= k₁) (P₂ >>= k₂)
bindκ-fsim k₁ k₂ pure kk pp = bindNoτ-fsim k₁ k₂ (pure→NoTauRoot k₁ pure) kk pp

-- `_>>_` (sequential composition of a √-terminating prefix) is an FSim congruence
>>-fsim : {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
        → FSim R P₁ P₂ → FSim S Q₁ Q₂ → FSim S (P₁ >> Q₁) (P₂ >> Q₂)
>>-fsim {Q₁ = Q₁} {Q₂ = Q₂} pp qq =
  Bind-fsim (λ _ → Q₁) (λ _ → Q₂) (>>-split Q₁) (λ _ → qq) pp
