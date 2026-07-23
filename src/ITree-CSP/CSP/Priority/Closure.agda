{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Layer 2 — per-operator `FinBr` closure lemmas (see
-- `docs/specs/priority-implementation-plan.md`).
--
-- Each lemma builds a `FinBr` certificate for a composed process so the
-- executable priority operator `Pri` (from `CSP.Priority.Base`) can be applied to
-- REAL CSP processes.  Since the `FinBr` redesign, a certificate carries a
-- `Dec (isStable t)` decision (plus `next`), so unstable nodes are witnessed by
-- ONE enabled τ — no finite enumeration of the (ℕ-polymorphic, hence infinite)
-- `fin`-indexed τ-family is needed.  This is what makes `⊓` inhabitable.
--
-- DONE this file:
--   * `finBr-Stop`      — `Stop = react ∅v ∅t`                       (stable)
--   * `finBr-prefix`    — `e ⟶ cont = react (Prefix-cont e cont) ∅t` (stable)
--   * `finBr-prefix₀`   — `e ⟶₀ P`  = `Prefix e (λ _ → P)`           (stable)
--   * `finBr-⊓`         — `P ⊓ Q = react ∅v (br2 P Q)`             (UNSTABLE)
--   * `finBr-Ret`/`finBr-Skip`  — `Ret r = ret r` (√ then deadlock; not stable)
--   * `finBr-Tau`       — `Tau P = sil P`  (τ then P; not stable)
--   * `finBr-div`       — `div = sil div`  (τ-loop; not stable; corecursive)
--   * `finBr-▷`         — `P ▷ Q` slide/timeout (always UNSTABLE; via ▷-*-elim)
--   * `finBr-□`         — `P □ Q` external choice (needs `DecEq R`; via □-*-elim;
--                         stable iff both operands stable; corecursive on choice τ)
--   * `finBr-rename`    — `renameInv P inv` (= `P ⟦ inv ⟧ⁱ`); stable iff `P` is
--                         (rename adds no τ); via `ren-τ-inv`/`ren-ev-inv`
--   * `finBr-∥`/`finBr-⦀` — `Par A merge P Q` / interleaving; stable iff both
--                         operands stable; `next` via `Par-τ-elim`/`Par-ev-elim`;
--                         the `evBoth` overlap successor is an inline `record`
--                         (guards the corecursion under the FinBr constructor)
--
-- Each is an INDEPENDENT top-level definition (partial commits fine).
--
-- `--safe`: no `postulate`, no `NON_TERMINATING`, no `--sized-types`, nothing
-- from `Classical`/`dne`.  Coinductive `next` is guarded (recursive `FinBr`
-- under the record, as in `finBr-deadlock`).
--
--   * `finBr-∖`         — `P ∖ A` hide, via a caller-supplied refusal certificate
--                         `ARefusal` (the undecidable "P offers no A-event" part);
--                         `stable?` = P-stability ∧ refusal; `next` via Hide-*-elim
--
-- ALL 14 operators are now closed.  Every lemma carries `chan-supp`/`chan-compl`.
--
-- `finBr-∖` reuses the caller's `ARefusal` because "P refuses A" is undecidable in
-- general (parallel sync couples it to value-level agreement — see the closure
-- report); the caller supplies that one decision, everything else is derived.
------------------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift; lower) renaming (suc to lsuc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
import Data.Maybe.Relation.Unary.Any as MAny
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; map; filter)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_; all?) renaming (lookup to all-lookup)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Priority.Closure {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree
open import Semantics.LTS {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import CSP.Priority.Base  {ℓ} {ℓe} {E}
open import CSP.Operators E-≟
open EventSet using (mem)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (▷-τ-elim; ▷-ev-elim;
         □-τ-elim; □evR; evP; evQ; evPQ; □-ev-elim;
         □τR; cP; cQ; sPQ; sQP; chP; chQ)
open import CSP.Laws.Traces.PrefixInversion E-≟ using (□-mt-empty)
open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (renameInv; extBranch; extBwd; extFwd; ext-linv; invRel; invPreimg)
open import CSP.Laws.Traces.TraceLawsRename {ℓ} {ℓe} {E}
  using (ren-τ-inv; ren-ev-inv; extBranch-just-inv)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (Par-τ-elim; ParτR; τL; τR; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (Hide-τ; Hide-hidden; Hide-τ-elim; HideτR; hτP; hτH;
         Hide-ev-elim; HideevR; heV; he√; fHide-react)

-- "P offers no A-event" — the refusal proposition hide's `stable?` needs.
RefusesA : ∀ {ℓr} {R : Set ℓr} (A : EventSet) (P : PTree E (ExtI E) R)
         → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
RefusesA A P = ∀ {B} {e : E B} {a : B} {P′ : PTree E (ExtI E) _}
             → P ─[ ev (evl (evLabel B e a)) ]─► P′ → ¬ A .mem (B , e) a

private
  -- extract the witness of a `just` from an `Is-just`, and its converse.
  is-just→just : ∀ {ℓ'} {X : Set ℓ'} {m : Maybe X} → Is-just m → Σ[ x ∈ X ] m ≡ just x
  is-just→just {m = just x} _ = x , refl

  ≡just→Is-just : ∀ {ℓ'} {X : Set ℓ'} {m : Maybe X} {x} → m ≡ just x → Is-just m
  ≡just→Is-just refl = MAny.just _

  -- a visible step of `P` at channel `(A₀,e₀)` ⇒ that channel is in P's support.
  vstep→chan∈ : ∀ {ℓr} {R : Set ℓr} {P : PTree E (ExtI E) R}
                  {A₀ : Set ℓ} {e₀ : E A₀} {a₀ : A₀} {t′}
              → (fp : FinBr P)
              → P ─[ ev (evl (evLabel A₀ e₀ a₀)) ]─► t′
              → (A₀ , e₀) ∈ FinBr.chan-supp fp
  vstep→chan∈ {A₀ = A₀} {e₀ = e₀} {a₀ = a₀} fp step with ev-inv step
  ... | vP , τcP , eqP , br = FinBr.chan-compl fp eqP (A₀ , e₀) a₀ (≡just→Is-just br)

  -- a stable node has no τ-step (inlined — DRImpliesFD is not --safe).
  stable-no-τ : ∀ {ℓr} {R : Set ℓr} {t M : PTree E (ExtI E) R}
              → isStable t → t ─[ τ ]─► M → ⊥
  stable-no-τ {t = t} st (sSil eq) with PTree.force t | eq
  ... | sil _ | refl = lower st
  stable-no-τ {t = t} st (sTau {i = i} {a = a} eq br) with PTree.force t | eq
  ... | react v τc | refl = case trans (sym (st i a)) br of λ ()

  -- read `isStable` off a react-forced node (both directions), given its force eq.
  st→τc∅ : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
             {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
         → PTree.force t ≡ react v τc → isStable t → ∀ i a → τc i a ≡ nothing
  st→τc∅ {t = t} eqf st with PTree.force t | eqf
  ... | react v τc | refl = st

  τc∅→st : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
             {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
         → PTree.force t ≡ react v τc → (∀ i a → τc i a ≡ nothing) → isStable t
  τc∅→st {t = t} eqf h with PTree.force t | eqf
  ... | react v τc | refl = h

  -- converse of `stable-no-τ` at a react node: no τ-step ⇒ stable (uses the
  -- ORIGINAL force eq to build the witnessing sTau, then `τc∅→st`).
  noτ→stable : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
                 {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                 {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
             → PTree.force t ≡ react v τc → (∀ {M} → ¬ (t ─[ τ ]─► M)) → isStable t
  noτ→stable {t = t} {τc = τc} eq noτ = τc∅→st {t = t} eq go
    where
      go : ∀ i a → τc i a ≡ nothing
      go i a with τc i a in eqa
      ... | nothing = refl
      ... | just M  = contradiction (sTau eq eqa) noτ

  -- hide is stable when P is stable and refuses A (YES direction, as the EXACT
  -- reduced Π so it matches the `stable?` goal): a hidden-τ would be P's τ (⊥ by
  -- `stable-no-τ stP`) or a hidden A-event (⊥ by `refP`), via `Hide-τ-elim`.
  hide-stable : ∀ {ℓr} {R : Set ℓr} {A : EventSet} {P : PTree E (ExtI E) R}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
              → PTree.force P ≡ react vP τcP → isStable P → RefusesA A P
              → ∀ i a → hide-hTau A (react vP τcP) i a ≡ nothing
  hide-stable {A = A} {P = P} {vP = vP} {τcP = τcP} eqP stP refP i a
    with hide-hTau A (react vP τcP) i a in eqh
  ... | nothing = refl
  ... | just M  with Hide-τ-elim A P (sTau {i = i} {a = a} (fHide-react A P eqP) eqh)
  ...   | hτP P' Pτ refl      = ⊥-elim (stable-no-τ stP Pτ)
  ...   | hτH P' mem Pev refl = ⊥-elim (refP Pev mem)

  -- `□-mt` is `nothing` at a tag ⇒ the underlying operand τ-source is `nothing`
  -- (the internal `with viewT` produces `just (·□·)` when the source fires).
  □mt0∅ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
            (nP nQ : NodeKind E (ExtI E) R) (P Q : PTree E (ExtI E) R)
            {B : Set ℓ} {i : ExtI E B} {a : B}
        → □-mt nP nQ P Q ((Lift ℓ (Fin 1) × B) , pair fin i) (lift fzero , a) ≡ nothing
        → viewT nP (B , i) a ≡ nothing
  □mt0∅ nP nQ P Q {B} {i} {a} eq with viewT nP (B , i) a
  ... | just P' = case eq of λ ()
  ... | nothing = refl

  □mt1∅ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
            (nP nQ : NodeKind E (ExtI E) R) (P Q : PTree E (ExtI E) R)
            {B : Set ℓ} {i : ExtI E B} {a : B}
        → □-mt nP nQ P Q ((Lift ℓ (Fin 2) × B) , pair fin i) (lift (fsuc fzero) , a) ≡ nothing
        → viewT nQ (B , i) a ≡ nothing
  □mt1∅ nP nQ P Q {B} {i} {a} eq with viewT nQ (B , i) a
  ... | just Q' = case eq of λ ()
  ... | nothing = refl

  -- `extBranch` (the renamed τ-map) is everywhere-`nothing` iff the source τc is:
  -- `extBranch … τcP` pulls each target index back through `extBwd` to `τcP`.
  extBranch∅ : ∀ {ℓr} {Rr : Set ℓr}
                 {inv : (bt : AnyTypes E) → proj₁ bt → _}
                 {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) Rr))}
             → (∀ i a → τcP i a ≡ nothing)
             → ∀ i a → extBranch (invRel inv) (invPreimg inv) τcP i a ≡ nothing
  extBranch∅ {τcP = τcP} h (A , eι₂) a with extBwd eι₂
  ... | just eι₁ rewrite h (A , eι₁) a = refl
  ... | nothing  = refl

  extBranch∅-inv : ∀ {ℓr} {Rr : Set ℓr}
                 {inv : (bt : AnyTypes E) → proj₁ bt → _}
                 {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) Rr))}
             → (∀ i a → extBranch (invRel inv) (invPreimg inv) τcP i a ≡ nothing)
             → ∀ i a → τcP i a ≡ nothing
  extBranch∅-inv {inv = inv} {τcP = τcP} h (A , eι₁) a with τcP (A , eι₁) a in eqt
  ... | nothing = refl
  ... | just P₁ =
        case trans (sym (extBranch-just-inv {inv = inv} {τcP = τcP}
                          {eι₂ = extFwd eι₁} {eι₁ = eι₁} {a = a} (ext-linv eι₁) eqt))
                   (h (A , extFwd eι₁) a)
          of λ ()

------------------------------------------------------------------------
-- Stop  =  react ∅v ∅t   (stable, no offers, no τ, no transitions)
------------------------------------------------------------------------

-- `Stop` is stable (τc = ∅t) and has NO transitions of any kind.
finBr-Stop : ∀ {ℓr} {R : Set ℓr} → FinBr {R = R} Stop
FinBr.stable?    finBr-Stop     = yes (λ i a → refl)   -- τc = ∅t ⇒ stable
FinBr.chan-supp  finBr-Stop     = []                   -- ∅v offers nothing
FinBr.chan-compl finBr-Stop refl c x ()                -- ∅v c x = nothing ⇒ absurd
FinBr.next    finBr-Stop (sRet ())            -- react ≢ ret
FinBr.next    finBr-Stop (sSil ())            -- react ≢ sil
FinBr.next    finBr-Stop (sVis refl ())       -- v  = ∅v ⇒ `nothing ≡ just` absurd
FinBr.next    finBr-Stop (sTau refl ())       -- τc = ∅t ⇒ `nothing ≡ just` absurd

------------------------------------------------------------------------
-- Prefix  e ⟶ cont  =  react (Prefix-cont e cont) ∅t   (stable)
--
-- Its only transitions are visible: firing the offered channel `e` at some
-- value `x`, leading to `cont x`, whose `FinBr` is the hypothesis.  A visible
-- step at any OTHER channel is impossible (`Prefix-cont` = `nothing` there).
------------------------------------------------------------------------

-- if every residual `cont x` is finitary, so is the prefix `e ⟶ cont`.
finBr-prefix : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
                 {e : E A} {cont : A → PTree E (ExtI E) R}
             → (∀ x → FinBr (cont x)) → FinBr (Prefix e cont)
FinBr.stable?   (finBr-prefix H)          = yes (λ i a → refl)  -- τc = ∅t ⇒ stable
FinBr.chan-supp (finBr-prefix {A = A} {e = e} H) = (A , e) ∷ []  -- offers exactly channel (A,e)
-- the only Is-just offer is at the prefix channel (E-≟ split in Prefix-cont)
FinBr.chan-compl (finBr-prefix {A = A} {e = e} H) refl at a isj with E-≟ (A , e) at
... | yes refl = here refl
... | no  _    = contradiction isj (λ ())
FinBr.next    (finBr-prefix H) (sRet ())      -- react ≢ ret
FinBr.next    (finBr-prefix H) (sSil ())      -- react ≢ sil
FinBr.next    (finBr-prefix H) (sTau refl ()) -- τc = ∅t ⇒ `nothing ≡ just` absurd
-- visible step: split on whether the fired channel `at` is the prefix channel.
FinBr.next    (finBr-prefix {A = A} {e = e} {cont = cont} H)
              (sVis {at = at} {a = a} refl br) with E-≟ (A , e) at
... | yes refl = subst FinBr (just-injective br) (H a)  -- at = (A,e): target = cont a
... | no  _    = case br of λ ()                         -- else Prefix-cont = nothing

------------------------------------------------------------------------
-- Prefix₀  e ⟶₀ P  =  Prefix e (λ _ → P)   (constant continuation)
------------------------------------------------------------------------

-- specialisation of `finBr-prefix` to a value-independent continuation.
finBr-prefix₀ : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
                  {e : E A} {P : PTree E (ExtI E) R}
              → FinBr P → FinBr (Prefix₀ e P)
finBr-prefix₀ fp = finBr-prefix (λ _ → fp)

------------------------------------------------------------------------
-- Internal choice  P ⊓ Q  =  react ∅v (br2 P Q)   (UNSTABLE)
--
-- `br2 P Q (_ , fin) (lift fzero) = just P` and `… (lift (fsuc fzero)) = just Q`
-- (all other indices/values `nothing`).  So `P ⊓ Q` is unstable, witnessed by
-- the single τ at `fin {1}`/`lift fzero` → `P`.  Its only transitions are those
-- two τ-branches (to `P` / `Q`); no visible step (`v = ∅v`).
------------------------------------------------------------------------

-- if `P` and `Q` are finitary, so is `P ⊓ Q`.
finBr-⊓ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
        → FinBr P → FinBr Q → FinBr (P ⊓ Q)
-- unstable: the τ at `(Lift ℓ (Fin 1) , fin) , lift fzero` maps to `just P`,
-- contradicting any claim that every τ-branch is `nothing`.
FinBr.stable? (finBr-⊓ {P = P} {Q = Q} fp fq) =
  no (λ st → case st (Lift ℓ (Fin 1) , fin) (lift fzero) of λ ())
FinBr.chan-supp  (finBr-⊓ fp fq) = []                  -- ∅v offers nothing
FinBr.chan-compl (finBr-⊓ fp fq) refl c x ()           -- ∅v c x = nothing ⇒ absurd
-- no visible step; the two τ-branches go to P / Q; all else absurd.
FinBr.next (finBr-⊓ fp fq) (sRet ())
FinBr.next (finBr-⊓ fp fq) (sSil ())
FinBr.next (finBr-⊓ fp fq) (sVis refl ())                              -- v = ∅v
FinBr.next (finBr-⊓ fp fq) (sTau {i = _ , base _}   refl ())           -- br2 = nothing
FinBr.next (finBr-⊓ fp fq) (sTau {i = _ , pair _ _} refl ())           -- br2 = nothing
FinBr.next (finBr-⊓ fp fq) (sTau {i = _ , fin} {a = lift fzero}            refl br) =
  subst FinBr (just-injective br) fp                                   -- → P
FinBr.next (finBr-⊓ fp fq) (sTau {i = _ , fin} {a = lift (fsuc fzero)}     refl br) =
  subst FinBr (just-injective br) fq                                   -- → Q
FinBr.next (finBr-⊓ fp fq) (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))}  refl ())  -- br2 = nothing

------------------------------------------------------------------------
-- Terminal / silent primitives  (ret / sil nodes — never stable)
------------------------------------------------------------------------

-- `Ret r = ret r`: its only step is `√ r` to `deadlock`; not stable.
finBr-Ret : ∀ {ℓr} {R : Set ℓr} (r : R) → FinBr (Ret r)
FinBr.stable?    (finBr-Ret r)          = no lower     -- isStable (ret) = Lift ⊥
FinBr.chan-supp  (finBr-Ret r)          = []           -- ret offers nothing
FinBr.chan-compl (finBr-Ret r) ()                      -- force = ret ⇒ ret ≢ react
FinBr.next    (finBr-Ret r) (sRet refl) = finBr-deadlock
FinBr.next    (finBr-Ret r) (sSil eq)   = case eq of λ ()   -- ret ≢ sil
FinBr.next    (finBr-Ret r) (sVis eq _) = case eq of λ ()   -- ret ≢ react
FinBr.next    (finBr-Ret r) (sTau eq _) = case eq of λ ()   -- ret ≢ react

-- `Skip = Ret tt`.
finBr-Skip : ∀ {ℓr} → FinBr (Skip {ℓr})
finBr-Skip = finBr-Ret tt

-- `Tau P = sil P`: its only step is τ to `P`; not stable.
finBr-Tau : ∀ {ℓr} {R : Set ℓr} {P : PTree E (ExtI E) R} → FinBr P → FinBr (Tau P)
FinBr.stable?    (finBr-Tau fp)          = no lower    -- isStable (sil) = Lift ⊥
FinBr.chan-supp  (finBr-Tau fp)          = []          -- sil offers nothing
FinBr.chan-compl (finBr-Tau fp) ()                     -- force = sil ⇒ sil ≢ react
FinBr.next    (finBr-Tau fp) (sSil refl) = fp          -- τ → P
FinBr.next    (finBr-Tau fp) (sRet eq)   = case eq of λ ()   -- sil ≢ ret
FinBr.next    (finBr-Tau fp) (sVis eq _) = case eq of λ ()   -- sil ≢ react
FinBr.next    (finBr-Tau fp) (sTau eq _) = case eq of λ ()   -- sil ≢ react

-- `div = sil div`: a silent self-loop; not stable; `next` is corecursive.
finBr-div : ∀ {ℓr} {R : Set ℓr} → FinBr {R = R} div
FinBr.stable?    finBr-div          = no lower         -- isStable (sil) = Lift ⊥
FinBr.chan-supp  finBr-div          = []               -- sil offers nothing
FinBr.chan-compl finBr-div ()                          -- force = sil ⇒ sil ≢ react
FinBr.next    finBr-div (sSil refl) = finBr-div        -- τ → div (guarded corecursion)
FinBr.next    finBr-div (sRet eq)   = case eq of λ ()  -- sil ≢ ret
FinBr.next    finBr-div (sVis eq _) = case eq of λ ()  -- sil ≢ react
FinBr.next    finBr-div (sTau eq _) = case eq of λ ()  -- sil ≢ react

------------------------------------------------------------------------
-- Slide / timeout  P ▷ Q   (composite; `next` via ▷-τ-elim / ▷-ev-elim)
--
-- `force (P ▷ Q)` is `ret r` when `P` terminated, else
-- `react (viewV nP) (▷-slide nP Q)` — and the timeout τ (`▷-slide … (lift fzero) = just Q`)
-- is ALWAYS enabled, so `P ▷ Q` is NEVER stable (either `ret`, or has the timeout τ).
-- A visible step is P's step (to the same target); a τ is the timeout (→ Q) or P's own
-- τ sliding on (→ P′ ▷ Q).  `next` reuses `▷-ev-elim`/`▷-τ-elim`; self-corecursive.
------------------------------------------------------------------------

-- if `P` and `Q` are finitary, so is `P ▷ Q`.
finBr-▷ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
        → FinBr P → FinBr Q → FinBr (P ▷ Q)
-- unstable: `ret` (Lift ⊥) or the always-enabled timeout τ at
-- `(pair fin fin) , (lift fzero , _)` → `just Q`, contradicting stability.
FinBr.stable? (finBr-▷ {P = P} fp fq) with PTree.force P
... | ret r      = no lower
... | sil P'     =
  no (λ st → case st ((Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ())
... | react v τc =
  no (λ st → case st ((Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ())
-- offers exactly P's channels (the timeout/slide affect only τ, not offers).
FinBr.chan-supp (finBr-▷ fp fq) = FinBr.chan-supp fp
FinBr.chan-compl (finBr-▷ {P = P} fp fq) eq at a isj with PTree.force P in eqP
... | ret r        = case eq of λ ()
... | sil P'       = case eq of λ { refl → contradiction isj (λ ()) }   -- v = ∅v
... | react vP τcP = case eq of λ { refl → FinBr.chan-compl fp eqP at a isj }
-- visible step of `P ▷ Q` is a visible step of `P` (same target).
FinBr.next (finBr-▷ {P = P} {Q = Q} fp fq) (sRet eqf)      = FinBr.next fp (▷-ev-elim P Q (sRet eqf))
FinBr.next (finBr-▷ {P = P} {Q = Q} fp fq) (sVis eqf breq) = FinBr.next fp (▷-ev-elim P Q (sVis eqf breq))
-- τ step: timeout (→ Q) or P's τ sliding on (→ P′ ▷ Q).
FinBr.next (finBr-▷ {P = P} {Q = Q} fp fq) (sSil eqf) with ▷-τ-elim P Q (sSil eqf)
... | inj₁ refl             = fq
... | inj₂ (P' , Pτ , refl) = finBr-▷ (FinBr.next fp Pτ) fq
FinBr.next (finBr-▷ {P = P} {Q = Q} fp fq) (sTau eqf breq) with ▷-τ-elim P Q (sTau eqf breq)
... | inj₁ refl             = fq
... | inj₂ (P' , Pτ , refl) = finBr-▷ (FinBr.next fp Pτ) fq

------------------------------------------------------------------------
-- External choice  P □ Q   (composite; needs `DecEq R`; `next` via □-*-elim)
--
-- `stable?`:  `P □ Q` is stable iff BOTH operands are stable react nodes (`□-mt`
-- with both τ-parts empty).  A terminated (`ret`) or silent (`sil`) operand
-- always leaves an enabled τ (commit-/slide-tag), so those are unstable; the
-- both-`react` case is decided from the operands' own `stable?` (via `□-mt-empty`
-- for `yes`; for `no`, an enabled `□-mt` τ is recovered from `¬ isStable operand`).
--
-- `next`:  a visible/√ step is P's, Q's, or both (→ P₁ ⊓ Q₁); a τ is a commit
-- (→ P / Q), a slide (→ P′ ▷ Q / Q′ ▷ P), or a choice-preserving τ (→ P′ □ Q /
-- P □ Q′).  Reuses `□-ev-elim`/`□-τ-elim`; corecursive on the choice cases.
------------------------------------------------------------------------

-- if `P` and `Q` are finitary, so is `P □ Q`.
finBr-□ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
        → FinBr P → FinBr Q → FinBr (P □ Q)
-- stability decision, by cases on the operands' forced nodes
FinBr.stable? (finBr-□ {P = P} {Q = Q} fp fq) with PTree.force P in eqP | PTree.force Q in eqQ
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = no lower                                            -- ret r  ⇒ Lift ⊥
...   | no  _    = no (λ st → case st (Lift ℓ (Fin 1) , fin) (lift fzero) of λ ())  -- br2 → P
FinBr.stable? (finBr-□ {P = P} {Q = Q} fp fq) | ret rP | sil Q'      =
  no (λ st → case st ((Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ())  -- □-slide-RQ tag0 → P
FinBr.stable? (finBr-□ {P = P} {Q = Q} fp fq) | ret rP | react vQ τcQ =
  no (λ st → case st ((Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ())  -- □-slide-RQ tag0 → P
FinBr.stable? (finBr-□ {P = P} {Q = Q} fp fq) | sil P'      | ret rQ =
  no (λ st → case st ((Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ())  -- □-slide-PR tag0 → Q
FinBr.stable? (finBr-□ {P = P} {Q = Q} fp fq) | react vP τcP | ret rQ =
  no (λ st → case st ((Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ())  -- □-slide-PR tag0 → Q
-- both silent: □-mt tag0 = viewT (sil P') = just P'
FinBr.stable? (finBr-□ {P = P} {Q = Q} fp fq) | sil P' | sil Q' =
  no (λ st → case st ((Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ())
FinBr.stable? (finBr-□ {P = P} {Q = Q} fp fq) | sil P' | react vQ τcQ =
  no (λ st → case st ((Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ())
-- P react, Q silent: □-mt tag1 = viewT (sil Q') = just Q'
FinBr.stable? (finBr-□ {P = P} {Q = Q} fp fq) | react vP τcP | sil Q' =
  no (λ st → case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift (fsuc fzero) , lift fzero) of λ ())
-- both react: stable iff both operands stable (decide from their certificates)
FinBr.stable? (finBr-□ {P = P} {Q = Q} fp fq) | react vP τcP | react vQ τcQ
  with FinBr.stable? fp | FinBr.stable? fq
...   | yes eP | yes eQ = yes (□-mt-empty (st→τc∅ {t = P} eqP eP) (st→τc∅ {t = Q} eqQ eQ))
...   | no ¬eP | _      =
        no (λ emt → ¬eP (τc∅→st {t = P} eqP
              (λ { (Bj , cj) a → □mt0∅ (react vP τcP) (react vQ τcQ) P Q
                     (emt ((Lift ℓ (Fin 1) × Bj) , pair fin cj) (lift fzero , a)) })))
...   | yes _  | no ¬eQ =
        no (λ emt → ¬eQ (τc∅→st {t = Q} eqQ
              (λ { (Bj , cj) a → □mt1∅ (react vP τcP) (react vQ τcQ) P Q
                     (emt ((Lift ℓ (Fin 2) × Bj) , pair fin cj) (lift (fsuc fzero) , a)) })))
-- offers the UNION of the operands' channels (a □-offer is P's, Q's, or both).
FinBr.chan-supp (finBr-□ fp fq) = FinBr.chan-supp fp ++ FinBr.chan-supp fq
FinBr.chan-compl (finBr-□ {P = P} {Q = Q} fp fq) eq at a isj with is-just→just isj
... | t′ , br with □-ev-elim P Q (sVis eq br)
...   | evP Pstep  = ++⁺ˡ (vstep→chan∈ fp Pstep)
...   | evQ Qstep  = ++⁺ʳ (FinBr.chan-supp fp) (vstep→chan∈ fq Qstep)
...   | evPQ Ps Qs = ++⁺ˡ (vstep→chan∈ fp Ps)
-- transition inversion (uniform in the force cases via the □-*-elim lemmas)
FinBr.next (finBr-□ {P = P} {Q = Q} fp fq) (sRet eqf) = finBr-deadlock   -- √ ⇒ deadlock
FinBr.next (finBr-□ {P = P} {Q = Q} fp fq) (sVis eqf breq) with □-ev-elim P Q (sVis eqf breq)
... | evP Pstep      = FinBr.next fp Pstep
... | evQ Qstep      = FinBr.next fq Qstep
... | evPQ Ps Qs     = finBr-⊓ (FinBr.next fp Ps) (FinBr.next fq Qs)
FinBr.next (finBr-□ {P = P} {Q = Q} fp fq) (sSil eqf) with □-τ-elim P Q (sSil eqf)
... | cP refl            = fp
... | cQ refl            = fq
... | sPQ P' Pτ refl     = finBr-▷ (FinBr.next fp Pτ) fq
... | sQP Q' Qτ refl     = finBr-▷ (FinBr.next fq Qτ) fp
... | chP P' Pτ refl     = finBr-□ (FinBr.next fp Pτ) fq
... | chQ Q' Qτ refl     = finBr-□ fp (FinBr.next fq Qτ)
FinBr.next (finBr-□ {P = P} {Q = Q} fp fq) (sTau eqf breq) with □-τ-elim P Q (sTau eqf breq)
... | cP refl            = fp
... | cQ refl            = fq
... | sPQ P' Pτ refl     = finBr-▷ (FinBr.next fp Pτ) fq
... | sQP Q' Qτ refl     = finBr-▷ (FinBr.next fq Qτ) fp
... | chP P' Pτ refl     = finBr-□ (FinBr.next fp Pτ) fq
... | chQ Q' Qτ refl     = finBr-□ fp (FinBr.next fq Qτ)

------------------------------------------------------------------------
-- Renaming  renameInv P inv  =  P ⟦ inv ⟧ⁱ   (injective same-alphabet wrapper)
--
-- Renaming adds no τ (it relabels the τ-map bijectively via `extBwd`/`extFwd`),
-- so `renameInv P inv` is stable iff `P` is — decided from the operand
-- certificate through `extBranch∅`/`extBranch∅-inv`.  `next` lifts each step
-- back to a source step via `ren-τ-inv`/`ren-ev-inv`; self-corecursive.
------------------------------------------------------------------------

-- if `P` is finitary, so is its renaming `renameInv P inv`.  Channel support is
-- the FORWARD image of P's channels: `inv` (target→source) alone can't recover
-- the target channels, so a forward channel map `fwd` + coherence `fwd-ok`
-- (every `inv`-preimage channel maps forward to its target) is supplied.
finBr-rename : ∀ {ℓr} {Rr : Set ℓr}
                 {inv : (bt : AnyTypes E) → proj₁ bt → _}
                 {fwd : AnyTypes E → AnyTypes E}
                 {P : PTree E (ExtI E) Rr}
             → (fwd-ok : ∀ {bt b at a} → inv bt b ≡ just (at , a) → fwd at ≡ bt)
             → FinBr P → FinBr (renameInv P inv)
FinBr.stable? (finBr-rename {inv = inv} {P = P} fok fp) with PTree.force P in eqP
... | ret r        = no lower       -- force (renameInv P inv) = ret r ⇒ Lift ⊥
... | sil P₁       = no lower       -- force (renameInv P inv) = sil … ⇒ Lift ⊥
... | react vP τcP with FinBr.stable? fp
...   | yes eP = yes (extBranch∅ {inv = inv} (st→τc∅ {t = P} eqP eP))
...   | no ¬eP = no (λ emt → ¬eP (τc∅→st {t = P} eqP (extBranch∅-inv {inv = inv} emt)))
-- offers the forward image of P's channels.
FinBr.chan-supp (finBr-rename {fwd = fwd} fok fp) = map fwd (FinBr.chan-supp fp)
FinBr.chan-compl (finBr-rename {fwd = fwd} {P = P} fok fp) {v = v} eq at a isj with is-just→just isj
... | t′ , br with ren-ev-inv {P = P} (sVis eq br)
...   | inj₁ (src , a′ , bt , b , P₁ , Pev , inv-eq , refl , refl) =
        subst (_∈ map fwd (FinBr.chan-supp fp)) (fok inv-eq) (∈-map⁺ fwd (vstep→chan∈ fp Pev))
...   | inj₂ (r , () , _ , _)
-- √ ⇒ deadlock
FinBr.next (finBr-rename {inv = inv} {P = P} fok fp) (sRet eq) = finBr-deadlock
-- τ of the renaming is a τ of P (relabelled), then re-renamed
FinBr.next (finBr-rename {inv = inv} {P = P} fok fp) (sSil eq) with ren-τ-inv {inv = inv} {P = P} (sSil eq)
... | (P₁ , Pτ , refl) = finBr-rename fok (FinBr.next fp Pτ)
FinBr.next (finBr-rename {inv = inv} {P = P} fok fp) (sTau eq br) with ren-τ-inv {inv = inv} {P = P} (sTau eq br)
... | (P₁ , Pτ , refl) = finBr-rename fok (FinBr.next fp Pτ)
-- a visible step is a source visible step (→ renamed successor) or a √ (→ deadlock)
FinBr.next (finBr-rename {inv = inv} {P = P} fok fp) (sVis eq br) with ren-ev-inv {inv = inv} {P = P} (sVis eq br)
... | inj₁ (src , a′ , bt , b , P₁ , Pev , inv-eq , refl , refl) = finBr-rename fok (FinBr.next fp Pev)
... | inj₂ (r , () , _ , _)   -- a visible step cannot be a √ (evl … ≢ √)

------------------------------------------------------------------------
-- Parallel  Par A merge P Q   (the hardest; `next` via Par-*-elim)
--
-- Par's τ's are exactly P's and Q's own τ's (no sync-τ — synchronisation is on
-- VISIBLE events); so `Par A merge P Q` is stable iff `P` and `Q` are (a `ret`
-- or `sil` operand always leaves a slide/independent τ).  `next` splits a step
-- into P's/Q's/synchronised/interleaved via `Par-τ-elim`/`Par-ev-elim`; the
-- both-offer-outside-`A` overlap (`evBoth`) lands in an inline ⊓-style node whose
-- certificate is `finBr-parBoth`.  Corecursive on every case.
------------------------------------------------------------------------

-- helpers: `par-hTauR`/`par-hTauL` are `nothing` exactly where the live operand's
-- τ-map is (they just re-tag it).  Same clause discharges both directions.
private
  par-hTauR∅ : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
                 {A : EventSet} {merge : Mg R₁ R₂ R} {P : PTree E (ExtI E) R₁}
                 {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₂))}
             → (∀ i a → τcQ i a ≡ nothing)
             → ∀ i a → par-hTauR A merge P τcQ i a ≡ nothing
  par-hTauR∅ {τcQ = τcQ} h i a with τcQ i a | h i a
  ... | nothing | _ = refl

  par-hTauR∅-inv : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
                 {A : EventSet} {merge : Mg R₁ R₂ R} {P : PTree E (ExtI E) R₁}
                 {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₂))}
             → (∀ i a → par-hTauR A merge P τcQ i a ≡ nothing)
             → ∀ i a → τcQ i a ≡ nothing
  par-hTauR∅-inv {τcQ = τcQ} h i a with τcQ i a | h i a
  ... | nothing | _ = refl

  par-hTauL∅ : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
                 {A : EventSet} {merge : Mg R₁ R₂ R} {Q : PTree E (ExtI E) R₂}
                 {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₁))}
             → (∀ i a → τcP i a ≡ nothing)
             → ∀ i a → par-hTauL A merge τcP Q i a ≡ nothing
  par-hTauL∅ {τcP = τcP} h i a with τcP i a | h i a
  ... | nothing | _ = refl

  par-hTauL∅-inv : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
                 {A : EventSet} {merge : Mg R₁ R₂ R} {Q : PTree E (ExtI E) R₂}
                 {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₁))}
             → (∀ i a → par-hTauL A merge τcP Q i a ≡ nothing)
             → ∀ i a → τcP i a ≡ nothing
  par-hTauL∅-inv {τcP = τcP} h i a with τcP i a | h i a
  ... | nothing | _ = refl

  -- `par-pTau` (both live) is everywhere-`nothing` iff both operands' τc are.
  par-pTau∅ : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
                {A : EventSet} {merge : Mg R₁ R₂ R}
                {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₁))}
                {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₂))}
                {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₁))}
                {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₂))}
                {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
            → (∀ i a → τcP i a ≡ nothing) → (∀ i a → τcQ i a ≡ nothing)
            → ∀ i a → par-pTau A merge (react vP τcP) (react vQ τcQ) P Q i a ≡ nothing
  par-pTau∅ hP hQ (_ , base _)            a = refl
  par-pTau∅ hP hQ (_ , fin)               a = refl
  par-pTau∅ hP hQ (_ , pair (base _) _)   a = refl
  par-pTau∅ hP hQ (_ , pair (pair _ _) _) a = refl
  par-pTau∅ hP hQ (_ , pair fin i) (lift fzero , a)            rewrite hP (_ , i) a = refl
  par-pTau∅ hP hQ (_ , pair fin i) (lift (fsuc fzero) , a)     rewrite hQ (_ , i) a = refl
  par-pTau∅ hP hQ (_ , pair fin i) (lift (fsuc (fsuc _)) , a)  = refl

  -- `par-pTau` `nothing` at a tag ⇒ the operand's τ-source is `nothing`.
  par-pTau0∅-inv : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
                {A : EventSet} {merge : Mg R₁ R₂ R}
                (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                {B : Set ℓ} {i : ExtI E B} {a : B}
            → par-pTau A merge nP nQ P Q ((Lift ℓ (Fin 1) × B) , pair fin i) (lift fzero , a) ≡ nothing
            → viewT nP (B , i) a ≡ nothing
  par-pTau0∅-inv nP nQ P Q {B} {i} {a} eq with viewT nP (B , i) a
  ... | just P' = case eq of λ ()
  ... | nothing = refl

  par-pTau1∅-inv : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
                {A : EventSet} {merge : Mg R₁ R₂ R}
                (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                {B : Set ℓ} {i : ExtI E B} {a : B}
            → par-pTau A merge nP nQ P Q ((Lift ℓ (Fin 2) × B) , pair fin i) (lift (fsuc fzero) , a) ≡ nothing
            → viewT nQ (B , i) a ≡ nothing
  par-pTau1∅-inv nP nQ P Q {B} {i} {a} eq with viewT nQ (B , i) a
  ... | just Q' = case eq of λ ()
  ... | nothing = refl

-- if `P` and `Q` are finitary, so is `Par A merge P Q`.  The `evBoth`
-- interleaving-overlap successor is built as an inline `record` (its `next`
-- guards the corecursive `finBr-∥` under the FinBr constructor — a top-level
-- helper would break syntactic guardedness).
finBr-∥ : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
            {A : EventSet} {merge : Mg R₁ R₂ R}
            {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
        → FinBr P → FinBr Q → FinBr (Par A merge P Q)
-- stability, by cases on the operands' forced nodes
FinBr.stable? (finBr-∥ {P = P} {Q = Q} fp fq) with PTree.force P in eqP | PTree.force Q in eqQ
... | ret r₁ | ret r₂ = no lower
... | ret r₁ | sil Q' = no lower
... | sil P' | ret r₂ = no lower
... | ret r₁ | react vQ τcQ with FinBr.stable? fq
...   | yes eQ = yes (par-hTauR∅ (st→τc∅ {t = Q} eqQ eQ))
...   | no ¬eQ = no (λ emt → ¬eQ (τc∅→st {t = Q} eqQ (par-hTauR∅-inv emt)))
FinBr.stable? (finBr-∥ {P = P} {Q = Q} fp fq) | react vP τcP | ret r₂ with FinBr.stable? fp
...   | yes eP = yes (par-hTauL∅ (st→τc∅ {t = P} eqP eP))
...   | no ¬eP = no (λ emt → ¬eP (τc∅→st {t = P} eqP (par-hTauL∅-inv emt)))
-- both silent / silent-react: a `sil` operand's τ (tag0/tag1) makes Par unstable
FinBr.stable? (finBr-∥ {P = P} {Q = Q} fp fq) | sil P' | sil Q' =
  no (λ st → case st ((Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ())
FinBr.stable? (finBr-∥ {P = P} {Q = Q} fp fq) | sil P' | react vQ τcQ =
  no (λ st → case st ((Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ())
FinBr.stable? (finBr-∥ {P = P} {Q = Q} fp fq) | react vP τcP | sil Q' =
  no (λ st → case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift (fsuc fzero) , lift fzero) of λ ())
-- both react: stable iff both operands stable
FinBr.stable? (finBr-∥ {P = P} {Q = Q} fp fq) | react vP τcP | react vQ τcQ
  with FinBr.stable? fp | FinBr.stable? fq
...   | yes eP | yes eQ = yes (par-pTau∅ (st→τc∅ {t = P} eqP eP) (st→τc∅ {t = Q} eqQ eQ))
...   | no ¬eP | _      =
        no (λ emt → ¬eP (τc∅→st {t = P} eqP
              (λ { (Bj , cj) a → par-pTau0∅-inv (react vP τcP) (react vQ τcQ) P Q
                     (emt ((Lift ℓ (Fin 1) × Bj) , pair fin cj) (lift fzero , a)) })))
...   | yes _  | no ¬eQ =
        no (λ emt → ¬eQ (τc∅→st {t = Q} eqQ
              (λ { (Bj , cj) a → par-pTau1∅-inv (react vP τcP) (react vQ τcQ) P Q
                     (emt ((Lift ℓ (Fin 2) × Bj) , pair fin cj) (lift (fsuc fzero) , a)) })))
-- offers the UNION of the operands' channels (sync/solo/both are operand offers).
FinBr.chan-supp (finBr-∥ fp fq) = FinBr.chan-supp fp ++ FinBr.chan-supp fq
FinBr.chan-compl (finBr-∥ {A = A} {merge = merge} {P = P} {Q = Q} fp fq) eq at a isj with is-just→just isj
... | t′ , br with Par-ev-elim A merge P Q (sVis eq br)
...   | evSync p Pev Qev  = ++⁺ˡ (vstep→chan∈ fp Pev)
...   | evL ¬p Pev        = ++⁺ˡ (vstep→chan∈ fp Pev)
...   | evR ¬p Qev        = ++⁺ʳ (FinBr.chan-supp fp) (vstep→chan∈ fq Qev)
...   | evBoth ¬p Pev Qev = ++⁺ˡ (vstep→chan∈ fp Pev)
-- transition inversion (uniform via Par-*-elim)
FinBr.next (finBr-∥ {A = A} {merge = merge} {P = P} {Q = Q} fp fq) (sRet eq) = finBr-deadlock
FinBr.next (finBr-∥ {A = A} {merge = merge} {P = P} {Q = Q} fp fq) (sSil eq) with Par-τ-elim A merge P Q (sSil eq)
... | τL P' Pτ refl = finBr-∥ (FinBr.next fp Pτ) fq
... | τR Q' Qτ refl = finBr-∥ fp (FinBr.next fq Qτ)
FinBr.next (finBr-∥ {A = A} {merge = merge} {P = P} {Q = Q} fp fq) (sTau eq br) with Par-τ-elim A merge P Q (sTau eq br)
... | τL P' Pτ refl = finBr-∥ (FinBr.next fp Pτ) fq
... | τR Q' Qτ refl = finBr-∥ fp (FinBr.next fq Qτ)
FinBr.next (finBr-∥ {A = A} {merge = merge} {P = P} {Q = Q} fp fq) (sVis eq br) with Par-ev-elim A merge P Q (sVis eq br)
... | evSync p Pev Qev  = finBr-∥ (FinBr.next fp Pev) (FinBr.next fq Qev)
... | evL ¬p Pev        = finBr-∥ (FinBr.next fp Pev) fq
... | evR ¬p Qev        = finBr-∥ fp (FinBr.next fq Qev)
... | evBoth ¬p Pev Qev = record
      { stable? = no (λ st → case st ((Lift ℓ (Fin 1)) , fin) (lift fzero) of λ ())
      ; chan-supp = []                                  -- ∅v offers nothing
      ; chan-compl = λ { refl c x () }                  -- ∅v c x = nothing ⇒ absurd
      ; next = λ { (sRet ())
                 ; (sSil ())
                 ; (sVis refl ())
                 ; (sTau {i = _ , base _}   refl ())
                 ; (sTau {i = _ , pair _ _} refl ())
                 ; (sTau {i = _ , fin} {a = lift fzero}           refl refl) → finBr-∥ (FinBr.next fp Pev) fq
                 ; (sTau {i = _ , fin} {a = lift (fsuc fzero)}    refl refl) → finBr-∥ fp (FinBr.next fq Qev)
                 ; (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl ()) }
      }

-- interleaving `P ⦀ Q = Par ∅ES (λ _ _ → tt) P Q` is the empty-sync instance.
finBr-⦀ : ∀ {ℓr} {P Q : PTree E (ExtI E) (⊤ {ℓr})} → FinBr P → FinBr Q → FinBr (P ⦀ Q)
finBr-⦀ = finBr-∥

------------------------------------------------------------------------
-- Hiding  P ∖ A   (composite; needs a caller-supplied refusal certificate)
--
-- `P ∖ A` is stable iff `P` is stable AND `P` offers no A-event.  The second
-- conjunct ("P refuses A") is undecidable in general (parallel sync couples it to
-- value-level agreement), so the CALLER supplies it as a coinductive certificate
-- `ARefusal` (a `Dec` of refusal at each reachable state).  With it, hide's
-- `stable?` becomes a total decision; `chan-supp` reuses `P`'s (completeness is
-- all `chan-compl` needs — a surviving offer is a non-A offer of `P`); `next`
-- inverts via `Hide-τ-elim`/`Hide-ev-elim`, self-corecursive.
------------------------------------------------------------------------

-- caller-supplied refusal certificate: a DECISION of "P offers no A-event" at
-- each reachable state, closed under transitions.
record ARefusal {ℓr} {R : Set ℓr} (A : EventSet) (P : PTree E (ExtI E) R)
              : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    refuses? : Dec (RefusesA A P)
    next     : ∀ {l t′} → P ─[ l ]─► t′ → ARefusal A t′

-- if `P` is finitary and refuses `A` (certified), so is `P ∖ A`.
finBr-∖ : ∀ {ℓr} {R : Set ℓr} {A : EventSet} {P : PTree E (ExtI E) R}
        → ARefusal A P → FinBr P → FinBr (P ∖ A)
-- stability: react case decided from P's stability + P's A-refusal
FinBr.stable? (finBr-∖ {A = A} {P = P} ar fpP) with PTree.force P in eqP
... | ret r  = no lower
... | sil c  = no lower
... | react vP τcP with FinBr.stable? fpP | ARefusal.refuses? ar
...   | yes stP | yes refP = yes (hide-stable eqP stP refP)
...   | no ¬stP | _ =
        no (λ st∖ → ¬stP (noτ→stable {t = P} eqP
              (λ Pτ → stable-no-τ (τc∅→st {t = P ∖ A} (fHide-react A P eqP) st∖) (Hide-τ A P Pτ))))
...   | yes _  | no ¬refP =
        no (λ st∖ → ¬refP
              (λ Pev mem → stable-no-τ (τc∅→st {t = P ∖ A} (fHide-react A P eqP) st∖) (Hide-hidden A P mem Pev)))
-- support: reuse P's channel support (over-approximation; completeness suffices)
FinBr.chan-supp (finBr-∖ ar fpP) = FinBr.chan-supp fpP
FinBr.chan-compl (finBr-∖ {A = A} {P = P} ar fpP) eq at a isj with is-just→just isj
... | t′ , br with Hide-ev-elim A P (sVis eq br)
...   | heV P' ¬c Pev = vstep→chan∈ fpP Pev
-- next: √ ⇒ deadlock; a surviving visible step / τ rebuilds the residual hide
FinBr.next (finBr-∖ {A = A} {P = P} ar fpP) (sRet eq) = finBr-deadlock
FinBr.next (finBr-∖ {A = A} {P = P} ar fpP) (sVis eq br) with Hide-ev-elim A P (sVis eq br)
... | heV P' ¬c Pev = finBr-∖ (ARefusal.next ar Pev) (FinBr.next fpP Pev)
FinBr.next (finBr-∖ {A = A} {P = P} ar fpP) (sSil eq) with Hide-τ-elim A P (sSil eq)
... | hτP P' Pτ refl      = finBr-∖ (ARefusal.next ar Pτ) (FinBr.next fpP Pτ)
... | hτH P' mem Pev refl = finBr-∖ (ARefusal.next ar Pev) (FinBr.next fpP Pev)
FinBr.next (finBr-∖ {A = A} {P = P} ar fpP) (sTau eq br) with Hide-τ-elim A P (sTau eq br)
... | hτP P' Pτ refl      = finBr-∖ (ARefusal.next ar Pτ) (FinBr.next fpP Pτ)
... | hτH P' mem Pev refl = finBr-∖ (ARefusal.next ar Pev) (FinBr.next fpP Pev)
