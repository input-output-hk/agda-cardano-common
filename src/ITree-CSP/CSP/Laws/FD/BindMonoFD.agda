{-# OPTIONS --guardedness #-}

-- FACT-SHAPED (`⊑FD → ⊑FD`) monotonicity for the BIND / SEQUENTIAL-COMPOSITION family:
--
--   `>>=-mono-⊑FD`     general bind    `P >>= k`   (needs `BindDivSplit k₂`, see below)
--   `bindNoτ-mono-⊑FD` τ-free-root continuation    (side condition discharged)
--   `bindκ-mono-⊑FD`   pure continuation           (side condition discharged)
--   `>>-mono-⊑FD`      sequential composition `P >> Q`  (side condition discharged)
--   `⨾⋆-mono-⊑FD` / `⨾Fin-mono-⊑FD`   the List- / Fin-indexed sequential folds
--
-- These are TRUE PRECONGRUENCES (shape 2 in `CSP.Laws.FD.IChoiceMonoFD`'s taxonomy):
-- `⊑FD` FACTS in, `⊑FD` fact out.  They SUPERSEDE and REPLACE the four shape-3
-- (`FSim → ⊑FD`) wrappers `Bind-mono-⊑FD` / `bindNoτ-mono-⊑FD` / `bindκ-mono-⊑FD` /
-- `>>-mono-⊑FD` that used to sit in `CSP.Laws.FD.LoopMonoFD` (now deleted; the general
-- one is renamed `>>=-mono-⊑FD` after the operator, matching the trace-level
-- `CSP.Laws.Traces` precedents `>>=-mono-L` / `>>=-mono-k`).  The FSim congruences
-- themselves (`Bind-fsim` &c.) stay in `CSP.Laws.FSim.BindCong` for FSim towers.
--
-- ── THE TWO SIDE CONDITIONS, AND WHY EACH IS NECESSARY ─────────────────────────────
--
-- (1) `BindDivSplit k₂` — the BIND KÖNIG STEP, needed for the `⊇D` half ONLY, and only
--     for the GENERAL bind.  Decomposing a divergence of `P₂ >>= k₂` means deciding
--     whether the infinite τ-chain stays inside the prefix `P₂` forever or crosses the
--     silent handover into some `k₂ r`; that is not constructively decidable.  Note the
--     split is on `k₂`, the RIGHT (refined) operand — it is the one being decomposed.
--     Exactly the hypothesis `Bind-fsim` takes, and it is DISCHARGED for each
--     specialisation below: `bind-noτ-split` for a τ-free-root continuation,
--     `pure→NoTauRoot` for a pure one, and `>>-split` for the constant continuation of
--     `_>>_`.  So `>>-mono-⊑FD` / `bindNoτ` / `bindκ` are UNCONDITIONAL.
--
-- (2) A SHARED RESULT LEVEL, `R S : Set ℓr` (not `R : Set ℓr`, `S : Set ℓs`).  This is a
--     LEVEL constraint, not a mathematical one, and it is forced by the SHAPE of
--     `_⊇F⊥_`: for `P : PTree E I R` with `R : Set ℓr` the ban set is pinned to
--     `Event√ R → Set ℓr`.  A failure of `P₂ >>= k₂` bans a set over `Event√ S`, and
--     transferring the still-in-prefix case through `P₁ ⊇F⊥ P₂` requires RETAGGING that
--     ban set over `Event√ R` (`banP` below) — which needs its codomain level to be
--     `ℓr`.  There is no way to move a `Set ℓs` to `Set ℓr` for unrelated levels
--     (`Lift` only goes UP, to `Set (ℓs ⊔ ℓr)`).  Precedent:
--     `CSP.Laws.FD.IterateMonoFD` pins `ℓr ≡ ℓ` outright for the same reason; this is
--     the weaker version (ANY shared level).  It costs nothing at the use sites: the
--     sequential folds `⨾⋆` / `⨾Fin` have `R ≡ S ≡ ⊤ {ℓr}`, and the FD refinements in
--     this repo are all at one level anyway.
--
-- ── POSTULATES: NONE LOCAL.  Inherited, per lemma: ─────────────────────────────────
--
--   * `>>=-mono-⊑FD`, and hence EVERY law here, inherits `Diverges-LEM` via
--     `CSP.Laws.FD.FDTransfer` (a plain LEM instance, certified from the single `dne` of
--     `CSP.Laws.ClassicalFromLEM`, Derivation 10).  It is used ONCE, in
--     `term-transfer`: to move the impl prefix's TERMINATING reach to the spec, the
--     spec's `√`-extended empty-ban failure has to be settled at a τ-normal form, and
--     whether that normal form exists is the classical bit.  A `⊑FD` fact carries
--     failures, and a `ret` state is not stable, so termination can only be observed
--     through the `√` tick — there is no constructive route.
--   * `>>-mono-⊑FD` (and the two folds, which are built from it) ADDITIONALLY inherits
--     `>>-Diverges→` (`CSP.Laws.FD.SeqDistR`) through `>>-split`; that postulate is
--     likewise certified from the same one `dne` (`>>-no-inf`, Derivation 4).  This is
--     the same inheritance the FSim analogue `>>-fsim` already had.
--   * `bindNoτ-mono-⊑FD` / `bindκ-mono-⊑FD` add NOTHING: their split is discharged
--     constructively by `bind-noτ-split` / `pure→NoTauRoot`.

open import Level using (Level; Lift; lift; lower) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
  renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.BindMonoFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim           {E = E} {I = ExtI E} using (_─[τ*]─►_)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Refuses; Offers)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊇F⊥_; _⊇D_; _⊑FD_; ⊑FD-refl; failures⊥; divergences; IsDivergence
        ; div-extension-closed; empty-div; Refuses-force-≡)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import CSP.Laws.FD.BindFD E-≟
  using (BindSplit; in-P; in-k; bind-bigstep-inv; bind-force-ret
        ; bind-div-intro-P; bind-div-intro-k
        ; bind-failures⊥-intro-P; bind-failures⊥-intro-k)
open import CSP.Laws.FSim.BindCong E-≟
  using (BindDivSplit; NoTauRoot; bind-noτ-split; pure→NoTauRoot; >>-split
        ; Bind-stable-normal; Bind-stable-P
        ; Bind-offer-elim-stable; Bind-offer-intro-evl)
open import CSP.Laws.FD.FDTransfer E-≟
  using (term→√failure; √-run-split-gen; div-√-truncate; ⟹-then-τ*)

-------------------------------------------------------------------------------------
-- PART 0 : the ban-set retag across the bind's carrier change  (side condition 2).
-------------------------------------------------------------------------------------

-- Retag a ban set of the COMPOSITE (`Event√ S`) as one of the PREFIX (`Event√ R`): keep
-- the carrier-independent visible part, ban no `√`.  Banning no `√` loses nothing: only a
-- STABLE state can refuse, a stable state never forces to a `ret`, and `√` is the one
-- event a non-`ret` node cannot offer.
banP : ∀ {ℓr} {R S : Set ℓr} → (Event√ S → Set ℓr) → Event√ R → Set ℓr
banP     B (evl l) = B (evl l)
banP {ℓr} B (√ _)  = Lift ℓr ⊥

-- REFUSAL ELIM: a still-in-prefix composite refusal IS a retagged prefix refusal (every
-- prefix offer survives the bind, and the composite offers no `√` to worry about).
bind-Refuses-P→ : ∀ {ℓr} {R S : Set ℓr}
                  (P′ : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                  {B : Event√ S → Set ℓr}
                → isStable P′ → Refuses (P′ >>= k) B → Refuses P′ (banP {R = R} B)
bind-Refuses-P→ {R = R} {S = S} P′ k {B} st (_ , noff) = st , h
  where
  h : ∀ (e : Event√ R) → banP {R = R} B e → ¬ Offers P′ e
  h (evl l) Bl off = noff (evl l) Bl (Bind-offer-intro-evl P′ k l off)
  -- a `√` is never in a retagged ban set, so this case is vacuous
  h (√ x)   Bx _   = lower Bx

-- REFUSAL INTRO: a retagged prefix refusal makes the composite refuse, for ANY
-- continuation (a stable prefix keeps the composite stable, and every composite offer
-- comes from an `evl` offer of the prefix).
bind-Refuses-P← : ∀ {ℓr} {R S : Set ℓr}
                  (P′ : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                  {B : Event√ S → Set ℓr}
                → Refuses P′ (banP {R = R} B) → Refuses (P′ >>= k) B
bind-Refuses-P← {S = S} P′ k {B} (st , noff) = Bind-stable-P P′ k st , h
  where
  h : ∀ (e : Event√ S) → B e → ¬ Offers (P′ >>= k) e
  h e Be off with Bind-offer-elim-stable P′ k st e off
  ... | l , refl , o = noff (evl l) Be o

-------------------------------------------------------------------------------------
-- PART 1 : ⊇F⊥ transfers a TERMINATING reach  (the one classical ingredient).
-------------------------------------------------------------------------------------

-- If the impl `P₂` visibly reaches a `ret r` state on a `√`-free trace, then so does the
-- spec `P₁` — or the spec already diverges there.  A `ret` state is NOT stable, so it is
-- no failure of its own; termination is observed through the `√` TICK, which
-- `term→√failure` turns into an (empty-ban) failure on `s ++ √ r ∷ []`.  Transfer that
-- through `⊇F⊥`, then either split the tick back off the spec's run
-- (`√-run-split-gen`, same `r`) or truncate the spec's divergence (`div-√-truncate`).
term-transfer : ∀ {ℓr} {R : Set ℓr} {P₁ P₂ : PTree E (ExtI E) R}
                {vs : List Event} {P′ : PTree E (ExtI E) R} {r : R}
              → P₁ ⊇F⊥ P₂ → P₂ ⟹⟨ map evl vs ⟩ P′ → force P′ ≡ ret r
              → (Σ[ Pᵣ ∈ PTree E (ExtI E) R ]
                   ((P₁ ⟹⟨ map evl vs ⟩ Pᵣ) × (force Pᵣ ≡ ret r)))
              ⊎ divergences P₁ (map evl vs)
term-transfer {ℓr = ℓr} {R = R} {P₁ = P₁} {vs = vs} {r = r} fF reach eqr =
  go (fF {map evl vs ++ √ r ∷ []} {λ _ → Lift ℓr ⊥} (inj₁ (term→√failure reach eqr)))
  where
  go : failures⊥ P₁ (map evl vs ++ √ r ∷ []) (λ _ → Lift ℓr ⊥)
     → (Σ[ Pᵣ ∈ PTree E (ExtI E) R ]
          ((P₁ ⟹⟨ map evl vs ⟩ Pᵣ) × (force Pᵣ ≡ ret r)))
     ⊎ divergences P₁ (map evl vs)
  go (inj₁ (_ , run√ , _)) with √-run-split-gen (map evl vs) run√
  ... | Pᵣ , run , eqf = inj₁ (Pᵣ , run , eqf)
  go (inj₂ dv) = inj₂ (div-√-truncate dv)

-- THE HANDOVER TRANSFER, failure form: the impl prefix terminated at `r` and the spec
-- continuation `k₁ r` fails⊥ on `s₂`, so the spec composite fails⊥ on the concatenation
-- (through the handover if the spec prefix also terminates, by divergence-extension if it
-- diverges in the prefix instead).
fail-handover : ∀ {ℓr} {R S : Set ℓr} (k₁ : R → PTree E (ExtI E) S)
                {P₁ P₂ P′ : PTree E (ExtI E) R} {r : R}
                {vs : List Event} {s₂ : List (Event√ S)} {B : Event√ S → Set ℓr}
              → P₁ ⊇F⊥ P₂ → P₂ ⟹⟨ map evl vs ⟩ P′ → force P′ ≡ ret r
              → failures⊥ (k₁ r) s₂ B
              → failures⊥ (P₁ >>= k₁) (map evl vs ++ s₂) B
fail-handover k₁ {P₁ = P₁} fP reach eqr fk⊥ with term-transfer fP reach eqr
... | inj₁ (_ , reach₁ , eqr₁) = bind-failures⊥-intro-k P₁ k₁ reach₁ eqr₁ fk⊥
... | inj₂ dv                  = inj₂ (div-extension-closed (bind-div-intro-P P₁ k₁ dv))

-- THE HANDOVER TRANSFER, divergence form (same case split as `fail-handover`)
div-handover : ∀ {ℓr} {R S : Set ℓr} (k₁ : R → PTree E (ExtI E) S)
               {P₁ P₂ P′ : PTree E (ExtI E) R} {r : R}
               {vs : List Event} {s₂ : List (Event√ S)}
             → P₁ ⊇F⊥ P₂ → P₂ ⟹⟨ map evl vs ⟩ P′ → force P′ ≡ ret r
             → divergences (k₁ r) s₂
             → divergences (P₁ >>= k₁) (map evl vs ++ s₂)
div-handover k₁ {P₁ = P₁} fP reach eqr dkr with term-transfer fP reach eqr
... | inj₁ (_ , reach₁ , eqr₁) = bind-div-intro-k P₁ k₁ reach₁ eqr₁ dkr
... | inj₂ dv                  = div-extension-closed (bind-div-intro-P P₁ k₁ dv)

-------------------------------------------------------------------------------------
-- PART 2 : the `⊇D` half.
-------------------------------------------------------------------------------------

-- DIVERGENCE ELIM keeping the handover witness.  `CSP.Laws.FD.BindFD.bind-div-elim`
-- discards the `force Pᵣ ≡ ret r` equation, and re-introducing a handover divergence
-- needs exactly that equation; so this variant retains it, mirroring what
-- `bind-failures⊥-elim` already does on the failure side.
bind-div-elim⁺ : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S) {s : List (Event√ S)}
   → divergences (P >>= k) s
   → (Σ[ vs ∈ List Event ] Σ[ P′ ∈ PTree E (ExtI E) R ] Σ[ sx ∈ List (Event√ S) ]
        ((P ⟹⟨ map evl vs ⟩ P′) × Diverges (P′ >>= k) × (s ≡ map evl vs ++ sx)))
   ⊎ (Σ[ r ∈ R ] Σ[ s₁ ∈ List Event ] Σ[ s₂ ∈ List (Event√ S) ]
        Σ[ Pᵣ ∈ PTree E (ExtI E) R ]
        ((P ⟹⟨ map evl s₁ ⟩ Pᵣ) × (force Pᵣ ≡ ret r) × divergences (k r) s₂
         × (s ≡ map evl s₁ ++ s₂)))
bind-div-elim⁺ P k d with bind-bigstep-inv P k (IsDivergence.reach d)
... | in-P {P′ = P′} {vs = vs} reachP weq =
      inj₁ (vs , P′ , IsDivergence.suffix d , reachP
           , subst Diverges weq (IsDivergence.divwit d)
           , IsDivergence.split d)
... | in-k {r = r} {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} reachP eqr reachk =
      inj₂ (r , s₁ , s₂ ++ IsDivergence.suffix d , Pᵣ , reachP , eqr
           , record
               { prefix  = s₂
               ; suffix  = IsDivergence.suffix d
               ; split   = refl
               ; witness = IsDivergence.witness d
               ; reach   = reachk
               ; divwit  = IsDivergence.divwit d
               }
           , trans (IsDivergence.split d)
                   (++-assoc (map evl s₁) s₂ (IsDivergence.suffix d)))

-- `_>>=_` is ⊇D-monotone in prefix and continuation, given the bind König split for the
-- refined continuation.  Handover divergences additionally need the FAILURE half of the
-- prefix refinement (`term-transfer` runs on `⊇F⊥`).
bind-mono-⊇D : ∀ {ℓr} {R S : Set ℓr} (k₁ k₂ : R → PTree E (ExtI E) S)
               {P₁ P₂ : PTree E (ExtI E) R}
             → BindDivSplit k₂
             → P₁ ⊇F⊥ P₂ → P₁ ⊇D P₂ → (∀ r → (k₁ r) ⊇D (k₂ r))
             → (P₁ >>= k₁) ⊇D (P₂ >>= k₂)
bind-mono-⊇D k₁ k₂ {P₁} {P₂} sp fP dP dk d with bind-div-elim⁺ P₂ k₂ d
-- HANDOVER: the divergence sits in the continuation, past a terminating prefix reach.
... | inj₂ (r , s₁ , s₂ , _ , reachP , eqr , dkr , seq) =
      subst (divergences (P₁ >>= k₁)) (sym seq)
            (div-handover k₁ fP reachP eqr (dk r dkr))
-- STILL IN THE PREFIX: decide with the König split where the infinite τ-chain lives.
... | inj₁ (vs , P′ , sx , reachP , dvB , seq) with sp P′ dvB
--   … inside the prefix: a prefix divergence, transferred by ⊇D and re-introduced.
...   | inj₁ dP′ =
        subst (divergences (P₁ >>= k₁)) (sym seq)
              (div-extension-closed (bind-div-intro-P P₁ k₁
                 (dP (record { prefix  = map evl vs ; suffix = []
                             ; split   = sym (++-identityʳ (map evl vs))
                             ; witness = P′ ; reach = reachP ; divwit = dP′ }))))
--   … past the handover: extend the prefix reach by the silent run, then hand over.
...   | inj₂ (_ , r , τrun , eqr , dkr) =
        subst (divergences (P₁ >>= k₁)) (sym seq)
              (div-extension-closed
                (subst (divergences (P₁ >>= k₁)) (++-identityʳ (map evl vs))
                  (div-handover k₁ fP (⟹-then-τ* reachP τrun) eqr
                     (dk r (empty-div dkr)))))

-------------------------------------------------------------------------------------
-- PART 3 : the `⊇F⊥` half (the FAILURE input; the divergence input is PART 2).
-------------------------------------------------------------------------------------

-- A stable failure of `P₂ >>= k₂` transfers to a failure⊥ of `P₁ >>= k₁`.  NO side
-- condition: `Bind-stable-normal` decides constructively whether the refusing state is
-- still in the prefix (retag the ban set, transfer, re-introduce) or past the handover
-- (the composite's refusal IS the continuation's, by the `ret` force-splice).
bind-mono-failures : ∀ {ℓr} {R S : Set ℓr} (k₁ k₂ : R → PTree E (ExtI E) S)
                     {P₁ P₂ : PTree E (ExtI E) R}
                   → P₁ ⊇F⊥ P₂ → (∀ r → (k₁ r) ⊇F⊥ (k₂ r))
                   → ∀ {s : List (Event√ S)} {B : Event√ S → Set ℓr}
                   → failures (P₂ >>= k₂) s B → failures⊥ (P₁ >>= k₁) s B
bind-mono-failures k₁ k₂ {P₁} {P₂} fP fk (W , run , ref)
  with bind-bigstep-inv P₂ k₂ run
-- HANDOVER: the refusal was reached inside `k₂ r`.
... | in-k {r = r} {s₁ = s₁} {s₂ = s₂} reachP eqr reachk =
      fail-handover k₁ fP reachP eqr (fk r (inj₁ (W , reachk , ref)))
-- STILL IN THE PREFIX: classify the stable composite.
... | in-P {P′ = P′} {vs = vs} reachP refl with Bind-stable-normal P′ k₂ (proj₁ ref)
--   … the prefix itself is stable: retag, transfer, re-introduce.
...   | inj₁ stP′ = go (fP (inj₁ (P′ , reachP , bind-Refuses-P→ P′ k₂ stP′ ref)))
        where
        go : failures⊥ P₁ (map evl vs) (banP {R = _} _) → failures⊥ (P₁ >>= k₁) (map evl vs) _
        go (inj₁ (P″ , reach″ , ref″)) =
             bind-failures⊥-intro-P P₁ k₁ reach″ (bind-Refuses-P← P″ k₁ ref″)
        go (inj₂ dv) = inj₂ (bind-div-intro-P P₁ k₁ dv)
--   … the prefix had already terminated at `r`, so the refusal is `k₂ r`'s.
...   | inj₂ (r , eqr , _) =
        subst (λ z → failures⊥ (P₁ >>= k₁) z _) (++-identityʳ (map evl vs))
          (fail-handover k₁ fP reachP eqr
            (fk r (inj₁ (k₂ r , ⟹-refl
                        , Refuses-force-≡ (sym (bind-force-ret P′ k₂ eqr)) ref))))

-------------------------------------------------------------------------------------
-- PART 4 : the general law, and its three unconditional specialisations.
-------------------------------------------------------------------------------------

-- `_>>=_` IS A ⊑FD-PRECONGRUENCE in prefix and continuation, given the bind König split
-- for the refined continuation `k₂` (side condition 1; see the header).
>>=-mono-⊑FD : ∀ {ℓr} {R S : Set ℓr} (k₁ k₂ : R → PTree E (ExtI E) S)
               {P₁ P₂ : PTree E (ExtI E) R}
             → BindDivSplit k₂
             → P₁ ⊑FD P₂ → (∀ r → (k₁ r) ⊑FD (k₂ r))
             → (P₁ >>= k₁) ⊑FD (P₂ >>= k₂)
>>=-mono-⊑FD k₁ k₂ {P₁} {P₂} sp (fP , dP) kk = F , D
  where
  D : (P₁ >>= k₁) ⊇D (P₂ >>= k₂)
  D = bind-mono-⊇D k₁ k₂ sp fP dP (λ r → proj₂ (kk r))
  F : (P₁ >>= k₁) ⊇F⊥ (P₂ >>= k₂)
  F (inj₁ f) = bind-mono-failures k₁ k₂ fP (λ r → proj₁ (kk r)) f
  F (inj₂ d) = inj₂ (D d)

-- `_>>=_` under a τ-FREE-ROOT refined continuation is a ⊑FD-precongruence,
-- UNCONDITIONALLY: a τ-less handover node cannot be crossed by an infinite τ-chain, so
-- the König split is constructive (`bind-noτ-split`).
bindNoτ-mono-⊑FD : ∀ {ℓr} {R S : Set ℓr} (k₁ k₂ : R → PTree E (ExtI E) S)
                   {P₁ P₂ : PTree E (ExtI E) R}
                 → NoTauRoot k₂
                 → P₁ ⊑FD P₂ → (∀ r → (k₁ r) ⊑FD (k₂ r))
                 → (P₁ >>= k₁) ⊑FD (P₂ >>= k₂)
bindNoτ-mono-⊑FD k₁ k₂ noτ pp kk = >>=-mono-⊑FD k₁ k₂ (bind-noτ-split k₂ noτ) pp kk

-- `_>>=_` under a PURE (`ret`-forcing) refined continuation is a ⊑FD-precongruence,
-- unconditionally — the shape the iterate / loop continuations have.
bindκ-mono-⊑FD : ∀ {ℓr} {R S : Set ℓr} (k₁ k₂ : R → PTree E (ExtI E) S)
                 {P₁ P₂ : PTree E (ExtI E) R}
               → (∀ r → Σ[ s ∈ S ] (force (k₂ r) ≡ ret s))
               → P₁ ⊑FD P₂ → (∀ r → (k₁ r) ⊑FD (k₂ r))
               → (P₁ >>= k₁) ⊑FD (P₂ >>= k₂)
bindκ-mono-⊑FD k₁ k₂ pure pp kk =
  bindNoτ-mono-⊑FD k₁ k₂ (pure→NoTauRoot k₂ pure) pp kk

-- SEQUENTIAL COMPOSITION IS A ⊑FD-PRECONGRUENCE IN BOTH OPERANDS, unconditionally: the
-- constant continuation's König split is `>>-split` (inheriting `>>-Diverges→`, exactly
-- as the FSim analogue `>>-fsim` does).
>>-mono-⊑FD : ∀ {ℓr} {R S : Set ℓr}
              {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
            → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂ → (P₁ >> Q₁) ⊑FD (P₂ >> Q₂)
>>-mono-⊑FD {R = R} {Q₁ = Q₁} {Q₂ = Q₂} pp qq =
  >>=-mono-⊑FD (λ _ → Q₁) (λ _ → Q₂) (>>-split {R = R} Q₂) pp (λ _ → qq)

-------------------------------------------------------------------------------------
-- PART 5 : the REPLICATED SEQUENTIAL folds, FACT-SHAPED.
--
-- ⚠ BOTH ARE EMPTY-BASED, like `⦀⋆`/`⦀Fin`/`□⋆`/`□Fin` and unlike `⨅⁺`/`⨅Fin`/`∥⁺`/
-- `∥Fin`: `Skip` IS the unit of `;`, so `⨾⋆ [] = Skip` and `⨾Fin zero f = Skip`
-- (`CSP.Operators`:358-364).  Hence the base case is `⊑FD-refl Skip`, NOT an operand
-- hypothesis, and the step is `>>-mono-⊑FD` — the two induction shapes are not
-- interchangeable.  Both fold with `_>>_` (never the general `_>>=_`), so they inherit
-- `>>-mono-⊑FD`'s discharge and need NO side condition of their own beyond the shared
-- result level, which is automatic here (`R ≡ S ≡ ⊤ {ℓr}`).
-------------------------------------------------------------------------------------

-- replicated sequential composition is a ⊑FD-precongruence, pointwise in its list
⨾⋆-mono-⊑FD : ∀ {ℓr} {Ps Qs : List (PTree E (ExtI E) (⊤ {ℓr}))}
            → Pointwise _⊑FD_ Ps Qs → ⨾⋆ Ps ⊑FD ⨾⋆ Qs
⨾⋆-mono-⊑FD []ᵖ       = ⊑FD-refl Skip
⨾⋆-mono-⊑FD (p ∷ᵖ ps) = >>-mono-⊑FD p (⨾⋆-mono-⊑FD ps)

-- the `Fin`-indexed sequential fold is a ⊑FD-precongruence, pointwise in its index
⨾Fin-mono-⊑FD : ∀ {ℓr} (n : ℕ) {f g : Fin n → PTree E (ExtI E) (⊤ {ℓr})}
              → (∀ i → f i ⊑FD g i) → ⨾Fin n f ⊑FD ⨾Fin n g
⨾Fin-mono-⊑FD zero    h = ⊑FD-refl Skip
⨾Fin-mono-⊑FD (suc n) h = >>-mono-⊑FD (h fzero) (⨾Fin-mono-⊑FD n (λ i → h (fsuc i)))
