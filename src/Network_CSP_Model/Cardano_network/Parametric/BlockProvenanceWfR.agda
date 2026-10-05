{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE RETURNING-TREE CARRIER `WfR` and its
-- sequential/iteration closure lemmas, split out of
-- `Parametric.BlockProvenanceNode` so that this generic development is
-- elaborated once, on its own, rather than alongside its Cardano
-- instantiation (the two together do not typecheck in reasonable time).
--
-- `BlockProvenance.Carrier`'s `Wf` is stated for unit-returning trees,
-- but the node's store body returns its new `Held` and its loops are
-- `iter`s over `_>>=_`-shaped bodies.  So `Body` below adds the
-- returning-tree carrier `WfR G s Inv M` — `Wf` plus `retR`: whatever
-- `M` returns satisfies `Inv` at every state at or above the current
-- one — with closure lemmas for exactly the operators `NodeLogic` uses
-- (`Ret`, `Stop`, `Prefix`, `Output`, `_□_` of STABLE operands, `_⊓_`,
-- `_>>=_`) and the `iter`/`loop`/`loop0` lemmas that land back in `Wf`.
-- The `_□_` lemma is deliberately restricted to stable operands (a
-- `react` with a pointwise-empty τ-part, `PrefixInversion.TEmpty`):
-- every `□` in the node logic is one, and it spares the module the
-- sliding and internal-choice τ-successors a `□` with a terminated
-- operand grows.  Duplicate held blocks DO make the `evPQ → _⊓_`
-- successor reachable in `offerHeld`, so `wfR-⊓` is not optional.
--
-- Nothing here is Cardano-specific: `Body` is parametric in the event
-- functor, exactly as `BlockProvenance.Carrier` is.  It nonetheless
-- lives beside that module rather than under `CSP.Laws.FD`, because it
-- opens `Carrier`, and no `CSP.Laws` module imports `CSP.Examples`.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.BlockProvenanceWfR where

open import Level using (Level; 0ℓ; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
  using ( PTree; ptree; NodeKind; ret; sil; react; AnyTypes; ExtI; ContinueType
        ; deadlock; sil-injective; react-injective )
import Semantics.LTS as LTS
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.BlockProvenance as BP

-- generic, over the same data as `BlockProvenance.Carrier` plus reflexivity of the
-- growth order (the `_>>=_` lemma steps the continuation at its own state)
module Body {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  (S B : Set)
  (Carries : (at : AnyTypes E) → proj₁ at → B → Set)
  (WA      : S → B → Set)
  (next    : LTS.Label {E = E} {I = ExtI E} (⊤ {0ℓ}) → S → S)
  (_≤_     : S → S → Set)
  (≤-refl  : ∀ {s} → s ≤ s)
  (≤-trans : ∀ {s₁ s₂ s₃} → s₁ ≤ s₂ → s₂ ≤ s₃ → s₁ ≤ s₃)
  (next-≤  : ∀ a s → s ≤ next a s) where

  open BP.Carrier E-≟ S B Carries WA next _≤_ ≤-trans next-≤
  open O {E = E} E-≟
    using ( Prefix; Prefix-cont; Output; Output-cont; Ret; Stop; _□_; _⊓_; _>>=_
          ; iter; iter-bind; loop; loop0; ∅t; _⦀_; ⦀⁺ )
  open import Semantics.LTS {E = E} {I = ExtI E}
    using (Label; Event√; ev; τ; evl; √; evLabel; _─[_]─►_; sRet; sSil; sVis; sTau)
  open import CSP.Laws.Bisim.DRCongruenceRep E-≟ using (Alpha; retarget)
  open import CSP.Laws.Traces.PrefixInversion E-≟ using (TEmpty; ∅t-empty; □-mt-empty)
  open import CSP.Laws.Traces.TraceLawsBind E-≟
    using (fBind-ret; fBind-sil; fBind-react; bindV-elim; bindT-elim)
  open import CSP.Laws.Bisim.IterCong E-≟
    using (fIter-r1; fIter-r2; fIter-sil; fIter-react; iterV-elim; iterT-elim)
  open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (fL-G)
  open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
    using ( □-τ-elim; cP; cQ; sPQ; sQP; chP; chQ
          ; □-ev-elim; evP; evQ; evPQ; □-force-ret-inv; br2-elim )

  private
    variable
      ℓr ℓr′ : Level
      R  : Set ℓr
      R′ : Set ℓr′
      G  : Alpha
      s  : S

  -- forget the return type of a label: `Wf`'s `OK`/`next` are stated at the unit type
  relabel : Label R → Label (⊤ {0ℓ})
  relabel τ            = τ
  relabel (ev (evl e)) = ev (evl e)
  relabel (ev (√ _))   = ev (√ tt)

  ------------------------------------------------------------------------
  -- Stable nodes
  ------------------------------------------------------------------------

  -- a STABLE node: a `react` with a pointwise-empty τ-part — every prefix, output,
  -- `Stop`, and (by `fL-G`/`□-mt-empty`) every `□` of stable nodes
  -- (a record, not a Σ: `Stable _P =?= Stable P` must solve `_P` outright, and a
  -- definition would unfold to a comparison of `force _P`, which blocks)
  -- (level and return type bound here, not generalised — see `WfR` below)
  record Stable {ℓr} {R : Set ℓr} (P : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    constructor stable
    field
      {vis}   : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
      {τpart} : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
      forceS  : PTree.force P ≡ react vis τpart
      emptyS  : TEmpty τpart
  open Stable

  -- a pure-visible node is stable
  stable-node : ∀ {P : PTree E (ExtI E) R} {v} → PTree.force P ≡ react v ∅t → Stable P
  stable-node eq = stable eq ∅t-empty

  -- external choice of stable nodes is stable
  stable-□ : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} → Stable P → Stable Q → Stable (P □ Q)
  stable-□ {P = P} {Q = Q} (stable eqP eP) (stable eqQ eQ) =
    stable (fL-G {P = P} {Q = Q} eqP eqQ _ _) (□-mt-empty eP eQ)

  -- a stable node makes no τ-step
  stable-noτ : {P : PTree E (ExtI E) R} → Stable P → ∀ {t} → P ─[ τ ]─► t → ⊥
  stable-noτ (stable eq _)  (sSil eqf) = case trans (sym eq) eqf of λ ()
  stable-noτ (stable eq em) (sTau {i = i} {a = a} eqf br) with react-injective (trans (sym eq) eqf)
  ... | refl , refl = case trans (sym (em i a)) br of λ ()

  ------------------------------------------------------------------------
  -- The carrier
  ------------------------------------------------------------------------

  -- `WfR G s Inv M`: `Wf` for a tree that may return — the same `nowR`/`stepR` (at the
  -- relabelled label), plus `retR`: whatever `M` returns satisfies `Inv` at every
  -- state at or above `s`
  -- (the level and the return type are bound HERE, not generalised: a `variable`-
  -- generalised `R` gets its own level binder, which then fails to match the `ℓr`
  -- written in the sort)
  record WfR {ℓr} {R : Set ℓr} (G : Alpha) (s : S) (Inv : S → R → Set)
             (M : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    coinductive
    field
      nowR  : ∀ {s′} → s ≤ s′ → ∀ {X} {e : E X} {a : X} {M′}
            → G (X , e) a → M ─[ ev (evl (evLabel X e a)) ]─► M′ → OK s′ (lbl e a)
      stepR : ∀ {s′} → s ≤ s′ → ∀ {a M′}
            → M ─[ a ]─► M′ → OK s′ (relabel a) → WfR G (next (relabel a) s′) Inv M′
      retR  : ∀ {s′} → s ≤ s′ → ∀ {r} → PTree.force M ≡ ret r → Inv s′ r
  open WfR public

  -- growing the state is a projection, as for `Wf`
  wfR-mono : ∀ {s′} {Inv : S → R → Set} {M} → s ≤ s′ → WfR G s Inv M → WfR G s′ Inv M
  wfR-mono le w .nowR  le′ g st  = nowR  w (≤-trans le le′) g st
  wfR-mono le w .stepR le′ st ok = stepR w (≤-trans le le′) st ok
  wfR-mono le w .retR  le′ eq    = retR  w (≤-trans le le′) eq

  -- the deadlocked tree does nothing and returns nothing
  wfR-deadlock : ∀ {Inv : S → R → Set} → WfR G s Inv deadlock
  wfR-deadlock .nowR  _ _ (sVis refl ())
  wfR-deadlock .stepR _ (sRet ())
  wfR-deadlock .stepR _ (sSil ())
  wfR-deadlock .stepR _ (sVis refl ())
  wfR-deadlock .stepR _ (sTau refl ())
  wfR-deadlock .retR  _ ()

  ------------------------------------------------------------------------
  -- Leaves: `Ret`, `Stop`, `Prefix`, `Output`
  ------------------------------------------------------------------------

  -- `Ret r` returns `r` and nothing else: `Inv` at every state above `s` is all it costs
  wfR-Ret : ∀ {Inv : S → R → Set} {r} → (∀ {s′} → s ≤ s′ → Inv s′ r) → WfR G s Inv (Ret r)
  wfR-Ret inv .nowR  _ _ (sVis () _)
  wfR-Ret inv .stepR _ (sRet _) _ = wfR-deadlock
  wfR-Ret inv .stepR _ (sSil ())
  wfR-Ret inv .stepR _ (sVis () _)
  wfR-Ret inv .stepR _ (sTau () _)
  wfR-Ret inv .retR  le refl = inv le

  -- `Stop` offers nothing
  wfR-Stop : ∀ {Inv : S → R → Set} → WfR G s Inv Stop
  wfR-Stop .nowR  _ _ (sVis refl ())
  wfR-Stop .stepR _ (sRet ())
  wfR-Stop .stepR _ (sSil ())
  wfR-Stop .stepR _ (sVis refl ())
  wfR-Stop .stepR _ (sTau refl ())
  wfR-Stop .retR  _ ()

  -- THE RELAY STEP.  A prefix `e ⟶ P` guarantees `OK` on its own channel if that is
  -- in `G`, and its continuation at `a` may ASSUME `OK s′ (lbl e a)` — the rely of an
  -- input — at the state the label leads to.  This is where a thread's register picks
  -- up the well-announcedness of the block it was handed.
  wfR-Prefix : ∀ {Inv : S → R → Set} {X} {e : E X} {P : X → PTree E (ExtI E) R}
             → (∀ {s′} → s ≤ s′ → ∀ a → G (X , e) a → OK s′ (lbl e a))
             → (∀ {s′} → s ≤ s′ → ∀ a → OK s′ (lbl e a) → WfR G (next (lbl e a) s′) Inv (P a))
             → WfR G s Inv (Prefix e P)
  wfR-Prefix {X = X} {e = e} g k .nowR le {a = a} gm (sVis {at = at} refl br)
    with E-≟ (X , e) at
  ... | no  _    = ⊥-elim (case br of λ ())
  ... | yes refl = g le a gm
  wfR-Prefix g k .stepR _ (sRet ())
  wfR-Prefix g k .stepR _ (sSil ())
  wfR-Prefix g k .stepR _ (sTau refl ())
  wfR-Prefix {X = X} {e = e} g k .stepR le (sVis {at = at} {a = a} refl br) ok
    with E-≟ (X , e) at
  ... | no  _    = ⊥-elim (case br of λ ())
  ... | yes refl = subst (WfR _ _ _) (just-injective br) (k le a ok)
  wfR-Prefix g k .retR _ ()

  -- an output `e ! v ⟶ Pk` guarantees `OK` on the one event it offers
  wfR-Output : ∀ {Inv : S → R → Set} {X} ⦃ _ : DecEq X ⦄ {e : E X} {v : X}
                 {Pk : PTree E (ExtI E) R}
             → (∀ {s′} → s ≤ s′ → G (X , e) v → OK s′ (lbl e v))
             → (∀ {s′} → s ≤ s′ → OK s′ (lbl e v) → WfR G (next (lbl e v) s′) Inv Pk)
             → WfR G s Inv (Output e v Pk)
  wfR-Output {X = X} {e = e} {v = v} g k .nowR le gm (sVis {at = at} {a = a} refl br)
    with E-≟ (X , e) at
  ... | no  _    = ⊥-elim (case br of λ ())
  ... | yes refl with a ≟ v
  ...   | no  _    = ⊥-elim (case br of λ ())
  ...   | yes refl = g le gm
  wfR-Output g k .stepR _ (sRet ())
  wfR-Output g k .stepR _ (sSil ())
  wfR-Output g k .stepR _ (sTau refl ())
  wfR-Output {X = X} {e = e} {v = v} g k .stepR le (sVis {at = at} {a = a} refl br) ok
    with E-≟ (X , e) at
  ... | no  _    = ⊥-elim (case br of λ ())
  ... | yes refl with a ≟ v
  ...   | no  _    = ⊥-elim (case br of λ ())
  ...   | yes refl = subst (WfR _ _ _) (just-injective br) (k le ok)
  wfR-Output g k .retR _ ()

  ------------------------------------------------------------------------
  -- Choice: `_⊓_`, and `_□_` of stable operands
  ------------------------------------------------------------------------

  -- internal choice: a τ to either operand, which stood still
  wfR-⊓ : ∀ {Inv : S → R → Set} {P Q : PTree E (ExtI E) R}
        → WfR G s Inv P → WfR G s Inv Q → WfR G s Inv (P ⊓ Q)
  wfR-⊓ wP wQ .nowR  _ _ (sVis refl ())
  wfR-⊓ wP wQ .stepR _ (sRet ())
  wfR-⊓ wP wQ .stepR _ (sSil ())
  wfR-⊓ wP wQ .stepR _ (sVis refl ())
  wfR-⊓ {P = P} {Q = Q} wP wQ .stepR {s′} le (sTau {i = i} {a = a} refl br) _
    with br2-elim P Q {i = i} {a = a} br
  ... | inj₁ refl = wfR-mono (≤-trans le (next-≤ τ s′)) wP
  ... | inj₂ refl = wfR-mono (≤-trans le (next-≤ τ s′)) wQ
  wfR-⊓ wP wQ .retR _ ()

  -- external choice of STABLE operands: a visible step is a step of one operand (or of
  -- both, landing in `_⊓_`), the two commit-τ's of `□-τ-elim` leave an operand as it
  -- was, and stability refutes its four slide/choice τ's
  -- (the operands are EXPLICIT: `_□_` is a `with` on both forces, so nothing recovers
  -- them from a goal `WfR … (P □ Q)`)
  wfR-□ : ⦃ _ : DecEq R ⦄ {Inv : S → R → Set} (P Q : PTree E (ExtI E) R)
        → Stable P → Stable Q → WfR G s Inv P → WfR G s Inv Q → WfR G s Inv (P □ Q)
  wfR-□ P Q sP sQ wP wQ .nowR le g st with □-ev-elim P Q st
  ... | evP  stP   = nowR wP le g stP
  ... | evQ  stQ   = nowR wQ le g stQ
  ... | evPQ stP _ = nowR wP le g stP
  wfR-□ P Q sP sQ wP wQ .stepR {s′} le {a = τ} st _ with □-τ-elim P Q st
  ... | cP  refl    = wfR-mono (≤-trans le (next-≤ τ s′)) wP
  ... | cQ  refl    = wfR-mono (≤-trans le (next-≤ τ s′)) wQ
  ... | sPQ _ stP _ = ⊥-elim (stable-noτ sP stP)
  ... | sQP _ stQ _ = ⊥-elim (stable-noτ sQ stQ)
  ... | chP _ stP _ = ⊥-elim (stable-noτ sP stP)
  ... | chQ _ stQ _ = ⊥-elim (stable-noτ sQ stQ)
  wfR-□ P Q sP sQ wP wQ .stepR le {a = ev _} st ok with □-ev-elim P Q st
  ... | evP  stP     = stepR wP le stP ok
  ... | evQ  stQ     = stepR wQ le stQ ok
  ... | evPQ stP stQ = wfR-⊓ (stepR wP le stP ok) (stepR wQ le stQ ok)
  wfR-□ P Q sP sQ wP wQ .retR le eq = retR wP le (□-force-ret-inv {P = P} {Q = Q} eq)

  ------------------------------------------------------------------------
  -- Sequential composition
  ------------------------------------------------------------------------

  -- `P >>= k`: on `P`'s `ret r` boundary the composite IS `k r`, whose well-formedness
  -- the continuation premise supplies from `Inv s′ r`; on `sil`/`react` the residual
  -- is again a bind.  The shape of `DRCongruenceRep.OffersOnly->>=`.
  wfR->>= : ∀ {Inv : S → R → Set} {Inv′ : S → R′ → Set}
              {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) R′}
          → WfR G s Inv P
          → (∀ {s′} → s ≤ s′ → ∀ r → Inv s′ r → WfR G s′ Inv′ (k r))
          → WfR G s Inv′ (P >>= k)
  wfR->>= {P = P} {k = k} wP wk .nowR le g (sVis {at = at} {a = a} eqf br)
    with PTree.force P in eqP
  ... | ret r      = nowR (wk le r (retR wP le eqP)) ≤-refl g (sVis eqf br)
  ... | sil c      = ⊥-elim (case eqf of λ ())
  ... | react v τc with bindV-elim k (react v τc)
                        (subst (λ f → f at a ≡ just _)
                               (sym (proj₁ (react-injective eqf)))
                               br)
  ...   | t , vv , _ = nowR wP le g (sVis eqP vv)
  wfR->>= {P = P} {k = k} wP wk .stepR {s′} le st ok with PTree.force P in eqP
  ... | ret r = stepR (wk le r (retR wP le eqP)) ≤-refl (retarget (sym (fBind-ret k P eqP)) st) ok
  ... | sil c with st
  ...   | sSil eqf with sil-injective (trans (sym (fBind-sil k P eqP)) eqf)
  ...     | refl   = wfR->>= (stepR wP le (sSil eqP) ok)
                             (λ le′ → wk (≤-trans le (≤-trans (next-≤ τ s′) le′)))
  wfR->>= {P = P} {k = k} wP wk .stepR le st ok | sil c | sRet eqf =
    ⊥-elim (case trans (sym (fBind-sil k P eqP)) eqf of λ ())
  wfR->>= {P = P} {k = k} wP wk .stepR le st ok | sil c | sVis eqf _ =
    ⊥-elim (case trans (sym (fBind-sil k P eqP)) eqf of λ ())
  wfR->>= {P = P} {k = k} wP wk .stepR le st ok | sil c | sTau eqf _ =
    ⊥-elim (case trans (sym (fBind-sil k P eqP)) eqf of λ ())
  wfR->>= {P = P} {k = k} wP wk .stepR {s′} le st ok | react v τc with st
  ...   | sVis {at = at} {a = a} eqf br
          with bindV-elim k (react v τc)
                 (subst (λ f → f at a ≡ just _)
                        (sym (proj₁ (react-injective (trans (sym (fBind-react k P eqP)) eqf))))
                        br)
  ...     | t , vv , refl = wfR->>= (stepR wP le (sVis eqP vv) ok)
                                    (λ le′ → wk (≤-trans le (≤-trans (next-≤ _ s′) le′)))
  wfR->>= {P = P} {k = k} wP wk .stepR {s′} le st ok | react v τc | sTau {i = i} {a = a} eqf br
    with bindT-elim k (react v τc)
           (subst (λ f → f i a ≡ just _)
                  (sym (proj₂ (react-injective (trans (sym (fBind-react k P eqP)) eqf))))
                  br)
  ...   | t , vv , refl = wfR->>= (stepR wP le (sTau eqP vv) ok)
                                  (λ le′ → wk (≤-trans le (≤-trans (next-≤ τ s′) le′)))
  wfR->>= {P = P} {k = k} wP wk .stepR le st ok | react v τc | sRet eqf =
    ⊥-elim (case trans (sym (fBind-react k P eqP)) eqf of λ ())
  wfR->>= {P = P} {k = k} wP wk .stepR le st ok | react v τc | sSil eqf =
    ⊥-elim (case trans (sym (fBind-react k P eqP)) eqf of λ ())
  wfR->>= {P = P} {k = k} wP wk .retR le eqf with PTree.force P in eqP
  ... | ret r      = retR (wk le r (retR wP le eqP)) ≤-refl eqf
  ... | sil c      = case eqf of λ ()
  ... | react v τc = case eqf of λ ()

  ------------------------------------------------------------------------
  -- Iteration, and the forever loops — landing in `Wf`
  ------------------------------------------------------------------------

  -- the return invariant of a loop body: the loop state carries `InvA`, an exit nothing
  InvSum : ∀ {A : Set ℓ} → (S → A → Set) → S → A ⊎ ⊤ {0ℓ} → Set
  InvSum InvA s (inj₁ a) = InvA s a
  InvSum InvA s (inj₂ _) = ⊤

  -- `iter-bind t k` is well-formed when the running body `t` is and every re-entry
  -- `k a` is, given the loop invariant `InvA` the body's return established.  The
  -- four `force t` clauses mirror `iter-bind`'s own (the shape of
  -- `DRCongruenceRep.OffersOnly-iter-bind`); the loop-back τ is where `retR` pays.
  wf-iter-bind : ∀ {A : Set ℓ} {t : PTree E (ExtI E) (A ⊎ ⊤ {0ℓ})}
                   {k : A → PTree E (ExtI E) (A ⊎ ⊤ {0ℓ})} {InvA : S → A → Set}
               → WfR G s (InvSum InvA) t
               → (∀ {s′} → s ≤ s′ → ∀ a → InvA s′ a → WfR G s′ (InvSum InvA) (k a))
               → Wf G s (iter-bind t k)
  wf-iter-bind {t = t} {k = k} wt wk .nowW le g (sVis {at = at} {a = a} eqf br)
    with PTree.force t in eqt
  ... | ret (inj₁ a′) = ⊥-elim (case eqf of λ ())
  ... | ret (inj₂ r)  = ⊥-elim (case eqf of λ ())
  ... | sil c         = ⊥-elim (case eqf of λ ())
  ... | react v τc with iterV-elim k (react v τc)
                        (subst (λ f → f at a ≡ just _)
                               (sym (proj₁ (react-injective eqf)))
                               br)
  ...   | t′ , vv , _ = nowR wt le g (sVis eqt vv)
  wf-iter-bind {t = t} {k = k} wt wk .stepW {s′} le st ok with PTree.force t in eqt
  ... | ret (inj₁ a′) with st
  ...   | sSil eqf with sil-injective (trans (sym (fIter-r1 k t eqt)) eqf)
  ...     | refl   = wf-iter-bind (wfR-mono (next-≤ τ s′) (wk le a′ (retR wt le eqt)))
                                  (λ le′ → wk (≤-trans le (≤-trans (next-≤ τ s′) le′)))
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | ret (inj₁ a′) | sRet eqf =
    ⊥-elim (case trans (sym (fIter-r1 k t eqt)) eqf of λ ())
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | ret (inj₁ a′) | sVis eqf _ =
    ⊥-elim (case trans (sym (fIter-r1 k t eqt)) eqf of λ ())
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | ret (inj₁ a′) | sTau eqf _ =
    ⊥-elim (case trans (sym (fIter-r1 k t eqt)) eqf of λ ())
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | ret (inj₂ r) with st
  ...   | sRet eqf = wf-deadlock
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | ret (inj₂ r) | sSil eqf =
    ⊥-elim (case trans (sym (fIter-r2 k t eqt)) eqf of λ ())
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | ret (inj₂ r) | sVis eqf _ =
    ⊥-elim (case trans (sym (fIter-r2 k t eqt)) eqf of λ ())
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | ret (inj₂ r) | sTau eqf _ =
    ⊥-elim (case trans (sym (fIter-r2 k t eqt)) eqf of λ ())
  wf-iter-bind {t = t} {k = k} wt wk .stepW {s′} le st ok | sil c with st
  ...   | sSil eqf with sil-injective (trans (sym (fIter-sil k t eqt)) eqf)
  ...     | refl   = wf-iter-bind (stepR wt le (sSil eqt) ok)
                                  (λ le′ → wk (≤-trans le (≤-trans (next-≤ τ s′) le′)))
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | sil c | sRet eqf =
    ⊥-elim (case trans (sym (fIter-sil k t eqt)) eqf of λ ())
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | sil c | sVis eqf _ =
    ⊥-elim (case trans (sym (fIter-sil k t eqt)) eqf of λ ())
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | sil c | sTau eqf _ =
    ⊥-elim (case trans (sym (fIter-sil k t eqt)) eqf of λ ())
  wf-iter-bind {t = t} {k = k} wt wk .stepW {s′} le st ok | react v τc with st
  ...   | sVis {at = at} {a = a} eqf br
          with iterV-elim k (react v τc)
                 (subst (λ f → f at a ≡ just _)
                        (sym (proj₁ (react-injective (trans (sym (fIter-react k t eqt)) eqf))))
                        br)
  ...     | t′ , vv , refl = wf-iter-bind (stepR wt le (sVis eqt vv) ok)
                                          (λ le′ → wk (≤-trans le (≤-trans (next-≤ _ s′) le′)))
  wf-iter-bind {t = t} {k = k} wt wk .stepW {s′} le st ok | react v τc | sTau {i = i} {a = a} eqf br
    with iterT-elim k (react v τc)
           (subst (λ f → f i a ≡ just _)
                  (sym (proj₂ (react-injective (trans (sym (fIter-react k t eqt)) eqf))))
                  br)
  ...   | t′ , vv , refl = wf-iter-bind (stepR wt le (sTau eqt vv) ok)
                                        (λ le′ → wk (≤-trans le (≤-trans (next-≤ τ s′) le′)))
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | react v τc | sRet eqf =
    ⊥-elim (case trans (sym (fIter-react k t eqt)) eqf of λ ())
  wf-iter-bind {t = t} {k = k} wt wk .stepW le st ok | react v τc | sSil eqf =
    ⊥-elim (case trans (sym (fIter-react k t eqt)) eqf of λ ())

  -- THE STATEFUL FOREVER LOOP: `loop body a = iter step a` with
  -- `step a = body a >>= λ a′ → Ret (inj₁ a′)`, so a body well-formed under a
  -- state-monotone loop invariant gives a well-formed loop
  wf-loop : ∀ {G : Alpha} {s : S} {A : Set ℓ} {body : A → PTree E (ExtI E) A}
              {InvA : S → A → Set} {a}
          → (∀ {s₁ s₂} → s₁ ≤ s₂ → ∀ a → InvA s₁ a → InvA s₂ a)
          → (∀ {s′} → s ≤ s′ → ∀ a → InvA s′ a → WfR G s′ InvA (body a))
          → InvA s a → Wf G s (loop body a)
  wf-loop {G = G} {s = s} {body = body} {InvA = InvA} mono wb inv =
    wf-iter-bind (step ≤-refl _ inv) step
    where
    -- one pass of the loop, its return re-establishing the invariant (`G`/`s` are the
    -- clause's, bound above: a `where` type would otherwise re-generalise them)
    step : ∀ {s′} → s ≤ s′ → ∀ a → InvA s′ a
         → WfR G s′ (InvSum InvA) (body a >>= λ a′ → Ret (inj₁ a′))
    step le a inv′ =
      wfR->>= (wb le a inv′) (λ _ a′ inv″ → wfR-Ret (λ le″ → mono le″ a′ inv″))

  -- the non-stateful loop: a body well-formed at every state above `s`
  wf-loop0 : ∀ {body : PTree E (ExtI E) (⊤ {ℓ})}
           → WfR G s (λ _ _ → ⊤ {0ℓ}) body → Wf G s (loop0 body)
  wf-loop0 wb = wf-loop (λ _ _ _ → tt) (λ le _ _ → wfR-mono le wb) tt

  -- replicated interleaving over a mapped list, one alphabet throughout
  wf-⦀⁺ : ∀ {ℓa} {A : Set ℓa} (f : A → PTree E (ExtI E) (⊤ {0ℓ})) (x : A) (xs : List A)
        → (∀ a → Wf G s (f a)) → Wf G s (⦀⁺ (f x) (map f xs))
  wf-⦀⁺ f x []       h = h x
  wf-⦀⁺ f x (y ∷ ys) h = wf-⦀ (h x) (wf-⦀⁺ f y ys h)

