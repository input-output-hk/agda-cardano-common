{-# OPTIONS --guardedness #-}

-- Trace laws for the (injective, same-alphabet) renaming wrapper `renameInv`.
-- `invPreimg` is a singleton ⇒ no fan-in ⇒ each visible step of `renameInv P inv`
-- comes from exactly one visible step of P, relabelled by `inv`.  We prove the
-- trace characterisation (intro/elim against a renaming relation on traces) and
-- trace monotonicity.  (The general relational `_⟦R¿preimg⟧` with fan-in is future.)

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsRename {ℓ ℓe} {E : Set ℓ → Set ℓe} where
open PTree

open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_; ⊑T-refl; ⊑T-trans)
open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)

private
  variable
    ℓr : Level
    Rr : Set ℓr

-- abbreviation
_⟦_⟧ⁱ : PTree E (ExtI E) Rr → ((bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁) → PTree E (ExtI E) Rr
P ⟦ inv ⟧ⁱ = renameInv P inv

-------------------------------------------------------------------------------------
-- Renaming relation on traces: each target event's label/value comes (via `inv`)
-- from the matching source event; √ passes through unchanged.
-------------------------------------------------------------------------------------

data RenTr {ℓr} {Rr : Set ℓr} (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
         : List (Event√ Rr) → List (Event√ Rr) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  []ᵣ : RenTr inv [] []
  evᵣ : ∀ {at a bt b s s′}
      → inv bt b ≡ just (at , a)
      → RenTr inv s s′
      → RenTr inv (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s)
                  (evl (evLabel (proj₁ bt) (proj₂ bt) b) ∷ s′)
  √ᵣ  : ∀ {r s s′} → RenTr inv s s′ → RenTr inv (√ r ∷ s) (√ r ∷ s′)

-------------------------------------------------------------------------------------
-- force-equations for `renameInv` (re-do `with force P` so it reduces).
-------------------------------------------------------------------------------------

force-ren-ret : ∀ {inv} {P : PTree E (ExtI E) Rr} {r}
              → PTree.force P ≡ ret r → PTree.force (P ⟦ inv ⟧ⁱ) ≡ ret r
force-ren-ret {P = P} eq with PTree.force P
... | ret _ = eq

force-ren-sil : ∀ {inv} {P P₁ : PTree E (ExtI E) Rr}
              → PTree.force P ≡ sil P₁ → PTree.force (P ⟦ inv ⟧ⁱ) ≡ sil (P₁ ⟦ inv ⟧ⁱ)
force-ren-sil {P = P} eq with PTree.force P
... | sil _ with refl ← eq = refl

force-ren-react : ∀ {inv} {P : PTree E (ExtI E) Rr}
                 {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) Rr))}
                 {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) Rr))}
               → PTree.force P ≡ react vP τcP
               → PTree.force (P ⟦ inv ⟧ⁱ)
                 ≡ react (λ bt b → rnFan (invRel inv) (invPreimg inv) (rnCollect vP (invPreimg inv bt b)))
                        (extBranch (invRel inv) (invPreimg inv) τcP)
force-ren-react {P = P} eq with PTree.force P
... | react _ _ with refl ← eq = refl

-------------------------------------------------------------------------------------
-- Reduction of the renamed visible offer for the injective wrapper (no fan-in):
-- at target (bt , b) with `inv bt b = just (at , a)` and the source offering
-- `vP at a = just P₁`, the renamed offer is exactly `just (P₁ ⟦inv⟧)`.
-------------------------------------------------------------------------------------

ren-vis-just :
    ∀ {inv} {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) Rr))}
      {bt b at a} {P₁ : PTree E (ExtI E) Rr}
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
      {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) Rr))}
      {A} {eι₂ eι₁ : ExtI E A} {a : A} {P₁ : PTree E (ExtI E) Rr}
  → extBwd eι₂ ≡ just eι₁ → τcP (A , eι₁) a ≡ just P₁
  → extBranch (invRel inv) (invPreimg inv) τcP (A , eι₂) a ≡ just (P₁ ⟦ inv ⟧ⁱ)
extBranch-just-inv {eι₂ = eι₂} eqb eqt with extBwd eι₂ | eqb
... | just eι₁ | refl rewrite eqt = refl

ren-τ-fwd : ∀ {inv} {P P₁ : PTree E (ExtI E) Rr}
          → P ─[ τ ]─► P₁ → (P ⟦ inv ⟧ⁱ) ─[ τ ]─► (P₁ ⟦ inv ⟧ⁱ)
ren-τ-fwd {inv = inv} {P = P} (sSil eq) = sSil (force-ren-sil {inv = inv} {P = P} eq)
ren-τ-fwd {inv = inv} {P = P} (sTau {τc = τcP} {i = A , eι₁} {a = a} eq br) =
  sTau {i = A , extFwd eι₁} {a = a}
       (force-ren-react {inv = inv} {P = P} eq)
       (extBranch-just-inv {inv = inv} {τcP = τcP} {eι₂ = extFwd eι₁} {eι₁ = eι₁} {a = a}
                           (ext-linv eι₁) br)

ren-ev-fwd : ∀ {inv} {P P₁ : PTree E (ExtI E) Rr} {at a bt b}
           → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P₁
           → inv bt b ≡ just (at , a)
           → (P ⟦ inv ⟧ⁱ) ─[ ev (evl (evLabel (proj₁ bt) (proj₂ bt) b)) ]─► (P₁ ⟦ inv ⟧ⁱ)
ren-ev-fwd {inv = inv} {P = P} {bt = bt} {b = b} (sVis {at = at} {a = a} eq br) eq-inv =
  sVis {at = bt} {a = b}
       (force-ren-react {inv = inv} {P = P} eq)
       (ren-vis-just {inv = inv} eq-inv br)

ren-√-fwd : ∀ {inv} {P : PTree E (ExtI E) Rr} {r}
          → PTree.force P ≡ ret r → (P ⟦ inv ⟧ⁱ) ─[ ev (√ r) ]─► deadlock
ren-√-fwd {inv = inv} {P = P} eq = sRet (force-ren-ret {inv = inv} {P = P} eq)

-------------------------------------------------------------------------------------
-- Trace introduction: a source big-step + a renaming of its trace gives a renamed
-- big-step.  (√ passes to `deadlock` on both sides; its tail is a deadlock trace.)
-------------------------------------------------------------------------------------

deadlock-⟹-[] : {W : PTree E (ExtI E) Rr} {s : List (Event√ Rr)}
              → deadlock ⟹⟨ s ⟩ W → s ≡ [] × W ≡ deadlock
deadlock-⟹-[] ⟹-refl              = refl , refl
deadlock-⟹-[] (⟹-τ (sSil ()) _)
deadlock-⟹-[] (⟹-τ (sTau refl ()) _)
deadlock-⟹-[] (⟹-ev (sRet ()) _)
deadlock-⟹-[] (⟹-ev (sVis refl ()) _)

-- INTRO: a source big-step + a renaming of its trace gives a renamed trace.
ren-trace-intro : ∀ {inv} {P P′ : PTree E (ExtI E) Rr} {s s′}
                → P ⟹⟨ s ⟩ P′ → RenTr inv s s′ → traces (renameInv P inv) s′
ren-trace-intro ⟹-refl []ᵣ = _ , ⟹-refl
ren-trace-intro (⟹-τ pτ rest) ren with ren-trace-intro rest ren
... | W , reach = W , ⟹-τ (ren-τ-fwd pτ) reach
ren-trace-intro (⟹-ev pev rest) (evᵣ inv-eq rest-ren) with ren-trace-intro rest rest-ren
... | W , reach = W , ⟹-ev (ren-ev-fwd pev inv-eq) reach
ren-trace-intro (⟹-ev (sRet eq) rest) (√ᵣ rest-ren) with deadlock-⟹-[] rest
... | refl , refl with rest-ren
...   | []ᵣ = deadlock , ⟹-ev (ren-√-fwd eq) ⟹-refl

-------------------------------------------------------------------------------------
-- force-INVERSIONS for renameInv (recover the source node shape).
-------------------------------------------------------------------------------------

force-ren-ret-inv : ∀ {inv} {P : PTree E (ExtI E) Rr} {r}
                  → PTree.force (P ⟦ inv ⟧ⁱ) ≡ ret r → PTree.force P ≡ ret r
force-ren-ret-inv {P = P} eq with PTree.force P
... | ret _    = eq
... | sil _    = case eq of λ ()
... | react _ _ = case eq of λ ()

force-ren-sil-inv : ∀ {inv} {P W : PTree E (ExtI E) Rr}
                  → PTree.force (P ⟦ inv ⟧ⁱ) ≡ sil W
                  → Σ[ P₁ ∈ PTree E (ExtI E) Rr ] (PTree.force P ≡ sil P₁ × W ≡ P₁ ⟦ inv ⟧ⁱ)
force-ren-sil-inv {P = P} eq with PTree.force P
... | ret _    = case eq of λ ()
... | sil P₁   = P₁ , refl , sym (sil-injective eq)
... | react _ _ = case eq of λ ()

force-ren-react-inv : ∀ {inv} {P : PTree E (ExtI E) Rr}
                       {v′ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) Rr))}
                       {τc′ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) Rr))}
                   → PTree.force (P ⟦ inv ⟧ⁱ) ≡ react v′ τc′
                   → Σ[ vP ∈ _ ] Σ[ τcP ∈ _ ]
                       (PTree.force P ≡ react vP τcP
                        × v′ ≡ (λ bt b → rnFan (invRel inv) (invPreimg inv) (rnCollect vP (invPreimg inv bt b)))
                        × τc′ ≡ extBranch (invRel inv) (invPreimg inv) τcP)
force-ren-react-inv {P = P} eq with PTree.force P
... | ret _      = case eq of λ ()
... | sil _      = case eq of λ ()
... | react vP τcP = vP , τcP , refl , sym (proj₁ (react-injective eq)) , sym (proj₂ (react-injective eq))

-------------------------------------------------------------------------------------
-- LTS step INVERSIONS: a renamed step comes from a source step (relabelled).
-------------------------------------------------------------------------------------

ren-τ-inv : ∀ {inv} {P W : PTree E (ExtI E) Rr}
          → (P ⟦ inv ⟧ⁱ) ─[ τ ]─► W → Σ[ P₁ ∈ PTree E (ExtI E) Rr ] (P ─[ τ ]─► P₁ × W ≡ P₁ ⟦ inv ⟧ⁱ)
ren-τ-inv {inv = inv} {P = P} (sSil eq) with force-ren-sil-inv {inv = inv} {P = P} eq
... | P₁ , eqP , eqW = P₁ , sSil eqP , eqW
ren-τ-inv {inv = inv} {P = P} (sTau {i = A , eι₂} {a = a} eq br)
  with force-ren-react-inv {inv = inv} {P = P} eq
... | vP , τcP , eqP , _ , refl with extBwd eι₂
...   | nothing = case br of λ ()
...   | just eι₁ with τcP (A , eι₁) a in eqt
...     | nothing  = case br of λ ()
...     | just t′  = t′ , sTau eqP eqt , sym (just-injective br)

ren-ev-inv : ∀ {inv} {P W : PTree E (ExtI E) Rr} {e′}
           → (P ⟦ inv ⟧ⁱ) ─[ ev e′ ]─► W
           → (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] Σ[ bt ∈ AnyTypes E ] Σ[ b ∈ proj₁ bt ]
                Σ[ P₁ ∈ PTree E (ExtI E) Rr ]
                  (P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P₁)
                  × (inv bt b ≡ just (at , a))
                  × (e′ ≡ evl (evLabel (proj₁ bt) (proj₂ bt) b))
                  × (W ≡ P₁ ⟦ inv ⟧ⁱ))
           ⊎ (Σ[ r ∈ Rr ] (e′ ≡ √ r) × (PTree.force P ≡ ret r) × (W ≡ deadlock))
ren-ev-inv {inv = inv} {P = P} (sRet eq) = inj₂ (_ , refl , force-ren-ret-inv {inv = inv} {P = P} eq , refl)
ren-ev-inv {inv = inv} {P = P} (sVis {at = bt} {a = b} eq br)
  with force-ren-react-inv {inv = inv} {P = P} eq
... | vP , τcP , eqP , refl , _ with inv bt b in eqinv
...   | nothing = case br of λ ()
...   | just (at , a) with vP at a in eqv
...     | nothing = case br of λ ()
...     | just P₁ = inj₁ (at , a , bt , b , P₁ , sVis eqP eqv , eqinv , refl , sym (just-injective br))

-------------------------------------------------------------------------------------
-- ELIM: a renamed trace comes from a source trace under the renaming relation.
-------------------------------------------------------------------------------------

ren-trace-elim : ∀ {inv} {P W : PTree E (ExtI E) Rr} {s′}
               → (P ⟦ inv ⟧ⁱ) ⟹⟨ s′ ⟩ W
               → Σ[ s ∈ List (Event√ Rr) ] Σ[ P′ ∈ PTree E (ExtI E) Rr ]
                   (P ⟹⟨ s ⟩ P′ × RenTr inv s s′)
ren-trace-elim ⟹-refl = [] , _ , ⟹-refl , []ᵣ
ren-trace-elim (⟹-τ step rest) with ren-τ-inv step
... | P₁ , Pτ , refl with ren-trace-elim rest
...   | s , P′ , Preach , ren = s , P′ , ⟹-τ Pτ Preach , ren
ren-trace-elim (⟹-ev step rest) with ren-ev-inv step
... | inj₁ (at , a , bt , b , P₁ , Pev , inv-eq , refl , refl) with ren-trace-elim rest
...   | s , P′ , Preach , ren =
        evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s , P′ , ⟹-ev Pev Preach , evᵣ inv-eq ren
ren-trace-elim (⟹-ev step rest) | inj₂ (r , refl , eqP , refl) with deadlock-⟹-[] rest
...   | refl , refl = √ r ∷ [] , deadlock , ⟹-ev (sRet eqP) ⟹-refl , √ᵣ []ᵣ

-------------------------------------------------------------------------------------
-- Trace monotonicity: elim the Q-side trace, transport via P ⊑T Q, re-intro.
-------------------------------------------------------------------------------------

renameInv-mono-⊑ᵀ : ∀ {inv} {P Q : PTree E (ExtI E) Rr}
                  → P ⊑T Q → (renameInv P inv) ⊑T (renameInv Q inv)
renameInv-mono-⊑ᵀ p⊑q s′ (W , reachQ) with ren-trace-elim reachQ
... | s , Q′ , Qreach , ren with p⊑q s (Q′ , Qreach)
...   | P′ , Preach = ren-trace-intro Preach ren
