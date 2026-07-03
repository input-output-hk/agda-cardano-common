{-# OPTIONS --guardedness #-}

-- Cross-alphabet rename preserves deadlock-freedom.
--
-- For the injective alphabet renaming `renameMap : PTree E₁ … → PTree E₂ …`
-- (induced by an event injection ι with partial inverse ι⁻¹), every √-free run
-- of `renameMap P` is the image of a √-free run of `P`, and every step of `P`
-- pushes forward to a step of `renameMap P`.  Hence `renameMap` neither creates
-- new stuck states nor makes a non-stuck state stuck, so
-- `DeadlockFree P → DeadlockFree (renameMap P)`.
--
-- Part 1 ports the single-step rename lemmas from
-- `CSP.Laws.Traces.TraceLawsRename` (there fixed to E₁=E₂=E) to the genuine
-- cross-alphabet header; the bodies transfer essentially verbatim because they
-- only use `CSP.Rename`'s cross-alphabet machinery.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Process_Trees

module CSP.Laws.Traces.RenameDeadlock {ℓ ℓe₁ ℓe₂}
  {E₁ : Set ℓ → Set ℓe₁} {E₂ : Set ℓ → Set ℓe₂}
  (ι      : ∀ {A} → E₁ A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e) where
open PTree
open import CSP.Rename {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv
import Semantics.LTS      {E = E₁} {I = ExtI E₁} as L1
import Semantics.LTS      {E = E₂} {I = ExtI E₂} as L2
import Semantics.Failures {E = E₁} {I = ExtI E₁} as F1
import Semantics.Failures {E = E₂} {I = ExtI E₂} as F2
import Semantics.Deadlock {E = E₁} {I = ExtI E₁} as D1
import Semantics.Deadlock {E = E₂} {I = ExtI E₂} as D2

private
  variable
    ℓr : Level
    Rr : Set ℓr

-- abbreviation: the injective-inverse renaming wrapper (source E₁ → target E₂)
_⟦_⟧ⁱ : PTree E₁ (ExtI E₁) Rr
      → ((bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁) → PTree E₂ (ExtI E₂) Rr
P ⟦ inv ⟧ⁱ = renameInv P inv

-- injectivity of `ret` on the target NodeKind (recover the returned value)
ret-inj₂ : ∀ {ℓr} {Rr : Set ℓr} {a b : Rr}
         → (ret {E = E₂} {I = ExtI E₂} a) ≡ ret b → a ≡ b
ret-inj₂ refl = refl

-------------------------------------------------------------------------------------
-- PART 1 — single-step rename lemmas (cross-alphabet port of TraceLawsRename)
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
-- force-equations for `renameInv` (re-do `with force P` so it reduces).
-------------------------------------------------------------------------------------

-- a source `ret` renames to a target `ret` of the same value
force-ren-ret : ∀ {inv} {P : PTree E₁ (ExtI E₁) Rr} {r : Rr}
              → PTree.force P ≡ ret r → PTree.force (renameInv P inv) ≡ ret r
force-ren-ret {P = P} eq rewrite eq = refl

-- a source `sil` renames to a target `sil` of the renamed continuation
force-ren-sil : ∀ {inv} {P P₁ : PTree E₁ (ExtI E₁) Rr}
              → PTree.force P ≡ sil P₁ → PTree.force (P ⟦ inv ⟧ⁱ) ≡ sil (P₁ ⟦ inv ⟧ⁱ)
force-ren-sil {P = P} eq with PTree.force P
... | sil _ with refl ← eq = refl

-- a source `react` renames to the target `react` built from `rnFan`/`extBranch`
force-ren-react : ∀ {inv} {P : PTree E₁ (ExtI E₁) Rr}
                 {vP : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr))}
                 {τcP : (i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (PTree E₁ (ExtI E₁) Rr))}
               → PTree.force P ≡ react vP τcP
               → PTree.force (P ⟦ inv ⟧ⁱ)
                 ≡ react (λ bt b → rnFan (invRel inv) (invPreimg inv) (rnCollect vP (invPreimg inv bt b)))
                        (extBranch (invRel inv) (invPreimg inv) τcP)
force-ren-react {P = P} eq with PTree.force P
... | react _ _ with refl ← eq = refl

-------------------------------------------------------------------------------------
-- Reduction of the renamed visible offer for the injective wrapper (no fan-in).
-------------------------------------------------------------------------------------

-- at a target (bt,b) with `inv bt b = just (at,a)` and source offering `vP at a = just P₁`,
-- the renamed offer is exactly `just (P₁ ⟦inv⟧)`.
ren-vis-just :
    ∀ {inv} {vP : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr))}
      {bt b at a} {P₁ : PTree E₁ (ExtI E₁) Rr}
  → inv bt b ≡ just (at , a) → vP at a ≡ just P₁
  → rnFan (invRel inv) (invPreimg inv) (rnCollect vP (invPreimg inv bt b))
    ≡ just (P₁ ⟦ inv ⟧ⁱ)
ren-vis-just {inv = inv} {vP = vP} {bt = bt} {b = b} eq-inv eq-v
  with inv bt b | eq-inv
... | just (at , a) | refl with vP at a | eq-v
...   | just P₁ | refl = refl

-------------------------------------------------------------------------------------
-- Forward LTS step lemmas: a source step lifts to a renamed step.
-------------------------------------------------------------------------------------

-- extBranch at a target index whose `extBwd` is `just eι₁` is the renamed source τ
extBranch-just-inv :
    ∀ {inv}
      {τcP : (i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (PTree E₁ (ExtI E₁) Rr))}
      {A} {eι₂ : ExtI E₂ A} {eι₁ : ExtI E₁ A} {a : A} {P₁ : PTree E₁ (ExtI E₁) Rr}
  → extBwd eι₂ ≡ just eι₁ → τcP (A , eι₁) a ≡ just P₁
  → extBranch (invRel inv) (invPreimg inv) τcP (A , eι₂) a ≡ just (P₁ ⟦ inv ⟧ⁱ)
extBranch-just-inv {eι₂ = eι₂} eqb eqt with extBwd eι₂ | eqb
... | just eι₁ | refl rewrite eqt = refl

-- a source τ-step renames to a target τ-step
ren-τ-fwd : ∀ {inv} {P P₁ : PTree E₁ (ExtI E₁) Rr}
          → P L1.─[ L1.τ ]─► P₁ → (P ⟦ inv ⟧ⁱ) L2.─[ L2.τ ]─► (P₁ ⟦ inv ⟧ⁱ)
ren-τ-fwd {inv = inv} {P = P} (L1.sSil eq) = L2.sSil (force-ren-sil {inv = inv} {P = P} eq)
ren-τ-fwd {inv = inv} {P = P} (L1.sTau {τc = τcP} {i = A , eι₁} {a = a} eq br) =
  L2.sTau {i = A , extFwd eι₁} {a = a}
       (force-ren-react {inv = inv} {P = P} eq)
       (extBranch-just-inv {inv = inv} {τcP = τcP} {eι₂ = extFwd eι₁} {eι₁ = eι₁} {a = a}
                           (ext-linv eι₁) br)

-- a source visible step, relabelled via `inv`, renames to a target visible step
ren-ev-fwd : ∀ {inv} {P P₁ : PTree E₁ (ExtI E₁) Rr}
             {at : AnyTypes E₁} {a : proj₁ at} {bt : AnyTypes E₂} {b : proj₁ bt}
           → P L1.─[ L1.ev (L1.evl (L1.evLabel (proj₁ at) (proj₂ at) a)) ]─► P₁
           → inv bt b ≡ just (at , a)
           → (P ⟦ inv ⟧ⁱ) L2.─[ L2.ev (L2.evl (L2.evLabel (proj₁ bt) (proj₂ bt) b)) ]─► (P₁ ⟦ inv ⟧ⁱ)
ren-ev-fwd {inv = inv} {P = P} {bt = bt} {b = b} (L1.sVis {at = at} {a = a} eq br) eq-inv =
  L2.sVis {at = bt} {a = b}
       (force-ren-react {inv = inv} {P = P} eq)
       (ren-vis-just {inv = inv} eq-inv br)

-- a source termination renames to a target √-step to deadlock
ren-√-fwd : ∀ {inv} {P : PTree E₁ (ExtI E₁) Rr} {r}
          → PTree.force P ≡ ret r → (P ⟦ inv ⟧ⁱ) L2.─[ L2.ev (L2.√ r) ]─► deadlock
ren-√-fwd {inv = inv} {P = P} eq = L2.sRet (force-ren-ret {inv = inv} {P = P} eq)

-------------------------------------------------------------------------------------
-- force-INVERSIONS for renameInv (recover the source node shape).
-------------------------------------------------------------------------------------

-- a renamed `ret` came from a source `ret`.  We case on a *named* node `nf` for
-- `force P` (via an auxiliary) so the goal never abstracts `force P`, then use the
-- forward `force-ren-*` lemmas to relate `force (renameInv P inv)` to that shape.
force-ren-ret-inv : ∀ {inv} {P : PTree E₁ (ExtI E₁) Rr} {r : Rr}
                  → PTree.force (renameInv P inv) ≡ ret r → PTree.force P ≡ ret r
force-ren-ret-inv {inv = inv} {P = P} {r = r} eq = aux (PTree.force P) refl
  where
  aux : (nf : NodeKind E₁ (ExtI E₁) _) → PTree.force P ≡ nf → PTree.force P ≡ ret r
  aux (ret r′)     eqP = trans eqP (cong ret (ret-inj₂ (trans (sym (force-ren-ret {inv = inv} {P = P} {r = r′} eqP)) eq)))
  aux (sil P₁)     eqP = case trans (sym (force-ren-sil {inv = inv} {P = P} eqP)) eq of λ ()
  aux (react vP τcP) eqP = case trans (sym (force-ren-react {inv = inv} {P = P} eqP)) eq of λ ()

-- a renamed `sil` came from a source `sil` (with renamed continuation).
force-ren-sil-inv : ∀ {inv} {P : PTree E₁ (ExtI E₁) Rr} {W : PTree E₂ (ExtI E₂) Rr}
                  → PTree.force (renameInv P inv) ≡ sil W
                  → Σ[ P₁ ∈ PTree E₁ (ExtI E₁) Rr ] (PTree.force P ≡ sil P₁ × W ≡ renameInv P₁ inv)
force-ren-sil-inv {inv = inv} {P = P} {W = W} eq = aux (PTree.force P) refl
  where
  aux : (nf : NodeKind E₁ (ExtI E₁) _) → PTree.force P ≡ nf
      → Σ[ P₁ ∈ PTree E₁ (ExtI E₁) _ ] (PTree.force P ≡ sil P₁ × W ≡ renameInv P₁ inv)
  aux (ret r)      eqP = case trans (sym (force-ren-ret {inv = inv} {P = P} eqP)) eq of λ ()
  aux (sil P₁)     eqP = P₁ , eqP , sym (sil-injective (trans (sym (force-ren-sil {inv = inv} {P = P} eqP)) eq))
  aux (react vP τcP) eqP = case trans (sym (force-ren-react {inv = inv} {P = P} eqP)) eq of λ ()

-- a renamed `react` came from a source `react` (recovering the offer/τ functions).
force-ren-react-inv : ∀ {inv} {P : PTree E₁ (ExtI E₁) Rr}
                       {v′ : (at : AnyTypes E₂) → ContinueType at (Maybe (PTree E₂ (ExtI E₂) Rr))}
                       {τc′ : (i : AnyTypes (ExtI E₂)) → ContinueType i (Maybe (PTree E₂ (ExtI E₂) Rr))}
                   → PTree.force (renameInv P inv) ≡ react v′ τc′
                   → Σ[ vP ∈ _ ] Σ[ τcP ∈ _ ]
                       (PTree.force P ≡ react vP τcP
                        × v′ ≡ (λ bt b → rnFan (invRel inv) (invPreimg inv) (rnCollect vP (invPreimg inv bt b)))
                        × τc′ ≡ extBranch (invRel inv) (invPreimg inv) τcP)
force-ren-react-inv {inv = inv} {P = P} {v′ = v′} {τc′ = τc′} eq = aux (PTree.force P) refl
  where
  aux : (nf : NodeKind E₁ (ExtI E₁) _) → PTree.force P ≡ nf
      → Σ[ vP ∈ _ ] Σ[ τcP ∈ _ ]
          (PTree.force P ≡ react vP τcP
           × v′ ≡ (λ bt b → rnFan (invRel inv) (invPreimg inv) (rnCollect vP (invPreimg inv bt b)))
           × τc′ ≡ extBranch (invRel inv) (invPreimg inv) τcP)
  aux (ret r)      eqP = case trans (sym (force-ren-ret {inv = inv} {P = P} eqP)) eq of λ ()
  aux (sil P₁)     eqP = case trans (sym (force-ren-sil {inv = inv} {P = P} eqP)) eq of λ ()
  aux (react vP τcP) eqP =
      vP , τcP , eqP
         , sym (proj₁ (react-injective (trans (sym (force-ren-react {inv = inv} {P = P} eqP)) eq)))
         , sym (proj₂ (react-injective (trans (sym (force-ren-react {inv = inv} {P = P} eqP)) eq)))

-------------------------------------------------------------------------------------
-- LTS step INVERSIONS: a renamed step comes from a source step (relabelled).
-------------------------------------------------------------------------------------

-- a renamed τ-step comes from a source τ-step
ren-τ-inv : ∀ {inv} {P : PTree E₁ (ExtI E₁) Rr} {W : PTree E₂ (ExtI E₂) Rr}
          → (P ⟦ inv ⟧ⁱ) L2.─[ L2.τ ]─► W
          → Σ[ P₁ ∈ PTree E₁ (ExtI E₁) Rr ] (P L1.─[ L1.τ ]─► P₁ × W ≡ P₁ ⟦ inv ⟧ⁱ)
ren-τ-inv {inv = inv} {P = P} (L2.sSil eq) with force-ren-sil-inv {inv = inv} {P = P} eq
... | P₁ , eqP , eqW = P₁ , L1.sSil eqP , eqW
ren-τ-inv {inv = inv} {P = P} (L2.sTau {i = A , eι₂} {a = a} eq br)
  with force-ren-react-inv {inv = inv} {P = P} eq
... | vP , τcP , eqP , _ , refl with extBwd eι₂
...   | nothing = case br of λ ()
...   | just eι₁ with τcP (A , eι₁) a in eqt
...     | nothing  = case br of λ ()
...     | just t′  = t′ , L1.sTau eqP eqt , sym (just-injective br)

-- a renamed visible step comes from a source visible step (relabelled) or a √
ren-ev-inv : ∀ {inv} {P : PTree E₁ (ExtI E₁) Rr} {W : PTree E₂ (ExtI E₂) Rr} {e′}
           → (P ⟦ inv ⟧ⁱ) L2.─[ L2.ev e′ ]─► W
           → (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] Σ[ bt ∈ AnyTypes E₂ ] Σ[ b ∈ proj₁ bt ]
                Σ[ P₁ ∈ PTree E₁ (ExtI E₁) Rr ]
                  (P L1.─[ L1.ev (L1.evl (L1.evLabel (proj₁ at) (proj₂ at) a)) ]─► P₁)
                  × (inv bt b ≡ just (at , a))
                  × (e′ ≡ L2.evl (L2.evLabel (proj₁ bt) (proj₂ bt) b))
                  × (W ≡ P₁ ⟦ inv ⟧ⁱ))
           ⊎ (Σ[ r ∈ Rr ] (e′ ≡ L2.√ r) × (PTree.force P ≡ ret r) × (W ≡ deadlock))
ren-ev-inv {inv = inv} {P = P} (L2.sRet eq) = inj₂ (_ , refl , force-ren-ret-inv {inv = inv} {P = P} eq , refl)
ren-ev-inv {inv = inv} {P = P} (L2.sVis {at = bt} {a = b} eq br)
  with force-ren-react-inv {inv = inv} {P = P} eq
... | vP , τcP , eqP , refl , _ with inv bt b in eqinv
...   | nothing = case br of λ ()
...   | just (at , a) with vP at a in eqv
...     | nothing = case br of λ ()
...     | just P₁ = inj₁ (at , a , bt , b , P₁ , L1.sVis eqP eqv , eqinv , refl , sym (just-injective br))

-------------------------------------------------------------------------------------
-- PART 2 — renameMap-specific deadlock lemmas (inv = ι-vis-inv)
-------------------------------------------------------------------------------------

-- forward witness for an injective ι: a source event has the target preimage (ι e).
ι-vis-inv-fwd : ∀ {A} (e : E₁ A) (a : A) → ι-vis-inv (A , ι e) a ≡ just ((A , e) , a)
ι-vis-inv-fwd e a rewrite ι-linv e = refl

-- any source move forward-pushes to a move of renameMap P (so renameMap P is
-- never "more stuck" than P).
rename-move-fwd : ∀ {ℓr} {Rr : Set ℓr} {P P₁ : PTree E₁ (ExtI E₁) Rr} {l}
                → P L1.─[ l ]─► P₁
                → Σ[ l′ ∈ L2.Label Rr ] Σ[ W₁ ∈ PTree E₂ (ExtI E₂) Rr ] (renameMap P L2.─[ l′ ]─► W₁)
rename-move-fwd {P = P} (L1.sSil eq) =
  L2.τ , _ , ren-τ-fwd {inv = ι-vis-inv} {P = P} (L1.sSil eq)
rename-move-fwd {P = P} (L1.sTau eq br) =
  L2.τ , _ , ren-τ-fwd {inv = ι-vis-inv} {P = P} (L1.sTau eq br)
rename-move-fwd {P = P} (L1.sVis {at = A , e} {a = a} eq br) =
  L2.ev (L2.evl (L2.evLabel A (ι e) a)) , _ ,
  ren-ev-fwd {inv = ι-vis-inv} {P = P} {at = A , e} {a = a} {bt = A , ι e} {b = a}
             (L1.sVis {at = A , e} {a = a} eq br) (ι-vis-inv-fwd e a)
rename-move-fwd {P = P} (L1.sRet eq) =
  L2.ev (L2.√ _) , deadlock , ren-√-fwd {inv = ι-vis-inv} {P = P} eq

-- a √-free run of renameMap P inverts to a √-free run of P (W ≡ renameMap P′).
rename-∖√-elim : ∀ {ℓr} {Rr : Set ℓr} {P : PTree E₁ (ExtI E₁) Rr}
                   {W : PTree E₂ (ExtI E₂) Rr} {s′}
               → renameMap P D2.⟹∖√⟨ s′ ⟩ W
               → Σ[ s ∈ List L1.Event ] Σ[ P′ ∈ PTree E₁ (ExtI E₁) Rr ]
                   (P D1.⟹∖√⟨ s ⟩ P′ × W ≡ renameMap P′)
rename-∖√-elim {P = P} D2.∖√-refl = [] , P , D1.∖√-refl , refl
rename-∖√-elim {P = P} (D2.∖√-τ st rest) with ren-τ-inv {inv = ι-vis-inv} {P = P} st
... | P₁ , Pτ , refl with rename-∖√-elim {P = P₁} rest
...   | s , P′ , reachP , eqW = s , P′ , D1.∖√-τ Pτ reachP , eqW
rename-∖√-elim {P = P} (D2.∖√-ev {e = e} st rest) with ren-ev-inv {inv = ι-vis-inv} {P = P} st
... | inj₁ (at , a , bt , b , P₁ , Pev , inv-eq , refl , refl) with rename-∖√-elim {P = P₁} rest
...   | s , P′ , reachP , eqW =
        L1.evLabel (proj₁ at) (proj₂ at) a ∷ s , P′ , D1.∖√-ev Pev reachP , eqW
rename-∖√-elim {P = P} (D2.∖√-ev {e = e} st rest) | inj₂ (r , eq√ , _ , _) = case eq√ of λ ()

-- rename preserves deadlock-freedom.
rename-DeadlockFree : ∀ {ℓr} {Rr : Set ℓr} {P : PTree E₁ (ExtI E₁) Rr}
                    → D1.DeadlockFree P → D2.DeadlockFree (renameMap P)
rename-DeadlockFree dfP reach stuck with rename-∖√-elim reach
... | s , P′ , reachP , refl =
      dfP reachP λ {l} {P₁} step →
        let (l′ , W₁ , rstep) = rename-move-fwd step in stuck rstep
