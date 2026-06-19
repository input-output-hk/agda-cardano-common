{-# OPTIONS --guardedness #-}

-- SPIKE: trace laws on the pure-react layer (mirroring CSP/Laws trace lemmas).
-- Batch 1: Stop and internal-choice (⊓).  Trace refinement P ⊑T Q ≡ traces Q ⊆ traces P.

open import Level using (Lift; lift)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.Traces.TraceLaws {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators  E-≟
open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E}
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL; ⊓-stepR; ⊓-τ-inv)

-------------------------------------------------------------------------------------
-- Stop: its only trace is the empty trace, and everything trace-refines it.
-------------------------------------------------------------------------------------

Stop-no-τ : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R} → ¬ (Stop ─[ τ ]─► t)
Stop-no-τ (sSil ())
Stop-no-τ (sTau refl ())

Stop-no-ev : ∀ {ℓr} {R : Set ℓr} {e} {t : PTree E (ExtI E) R} → ¬ (Stop ─[ ev e ]─► t)
Stop-no-ev (sRet ())
Stop-no-ev (sVis refl ())

Stop-traces-empty : ∀ {ℓr} {R : Set ℓr} {s} → traces (Stop {R = R}) s → s ≡ []
Stop-traces-empty (_ , ⟹-refl)      = refl
Stop-traces-empty (_ , ⟹-τ  st _)   = ⊥-elim (Stop-no-τ  st)
Stop-traces-empty (_ , ⟹-ev st _)   = ⊥-elim (Stop-no-ev st)

⊑ᵀ-Stop : ∀ {ℓr} {R : Set ℓr} (t : PTree E (ExtI E) R) → t ⊑T Stop
⊑ᵀ-Stop t s str with Stop-traces-empty str
... | refl = t , ⟹-refl

-------------------------------------------------------------------------------------
-- Internal choice: P ⊓ Q has all of P's and all of Q's traces.
-- (Each trace of P is a trace of P ⊓ Q after the τ-move P⊓Q ─[τ]─► P.)
-------------------------------------------------------------------------------------

⊑ᵀ-⊓-L : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ⊑T P
⊑ᵀ-⊓-L P Q s (P′ , tr) = P′ , ⟹-τ (⊓-stepL P Q) tr

⊑ᵀ-⊓-R : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ⊑T Q
⊑ᵀ-⊓-R P Q s (Q′ , tr) = Q′ , ⟹-τ (⊓-stepR P Q) tr

-- every trace of P ⊓ Q is a trace of P or of Q (its leading τ lands on one side)
⊓-trace-elim : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) {s}
             → traces (P ⊓ Q) s → traces P s ⊎ traces Q s
⊓-trace-elim P Q (_   , ⟹-refl)          = inj₁ (_ , ⟹-refl)
⊓-trace-elim P Q (end , ⟹-τ step rest) with ⊓-τ-inv P Q step
... | inj₁ refl = inj₁ (end , rest)
... | inj₂ refl = inj₂ (end , rest)
⊓-trace-elim P Q (_ , ⟹-ev (sRet ()) _)
⊓-trace-elim P Q (_ , ⟹-ev (sVis refl ()) _)

⊓-mono-⊑ᵀ : ∀ {ℓr} {R : Set ℓr} {P Q P′ Q′ : PTree E (ExtI E) R}
          → P ⊑T P′ → Q ⊑T Q′ → (P ⊓ Q) ⊑T (P′ ⊓ Q′)
⊓-mono-⊑ᵀ {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} p⊑ q⊑ s tr with ⊓-trace-elim P′ Q′ tr
... | inj₁ tP′ = ⊑ᵀ-⊓-L P Q s (p⊑ s tP′)
... | inj₂ tQ′ = ⊑ᵀ-⊓-R P Q s (q⊑ s tQ′)

-- internal choice is associative at the trace level (traces = traces P ∪ Q ∪ S either way).
-- NOTE: not a STRONG-bisim law — (P⊓Q)⊓S needs two τ's to reach P, P⊓(Q⊓S) only one — but
-- the trace sets coincide.  Both directions are pure ⊓-trace-elim / ⊑ᵀ-⊓-L/R reshuffling.
⊓-assoc-⊑-L : ∀ {ℓr} {R : Set ℓr} (P Q S : PTree E (ExtI E) R)
            → ((P ⊓ Q) ⊓ S) ⊑T (P ⊓ (Q ⊓ S))
⊓-assoc-⊑-L P Q S s tr with ⊓-trace-elim P (Q ⊓ S) tr
... | inj₁ tP  = ⊑ᵀ-⊓-L (P ⊓ Q) S s (⊑ᵀ-⊓-L P Q s tP)
... | inj₂ tQS with ⊓-trace-elim Q S tQS
...   | inj₁ tQ = ⊑ᵀ-⊓-L (P ⊓ Q) S s (⊑ᵀ-⊓-R P Q s tQ)
...   | inj₂ tS = ⊑ᵀ-⊓-R (P ⊓ Q) S s tS

⊓-assoc-⊑-R : ∀ {ℓr} {R : Set ℓr} (P Q S : PTree E (ExtI E) R)
            → (P ⊓ (Q ⊓ S)) ⊑T ((P ⊓ Q) ⊓ S)
⊓-assoc-⊑-R P Q S s tr with ⊓-trace-elim (P ⊓ Q) S tr
... | inj₂ tS  = ⊑ᵀ-⊓-R P (Q ⊓ S) s (⊑ᵀ-⊓-R Q S s tS)
... | inj₁ tPQ with ⊓-trace-elim P Q tPQ
...   | inj₁ tP = ⊑ᵀ-⊓-L P (Q ⊓ S) s tP
...   | inj₂ tQ = ⊑ᵀ-⊓-R P (Q ⊓ S) s (⊑ᵀ-⊓-L Q S s tQ)

⊓-assoc-≈T : ∀ {ℓr} {R : Set ℓr} (P Q S : PTree E (ExtI E) R)
           → (((P ⊓ Q) ⊓ S) ⊑T (P ⊓ (Q ⊓ S))) × ((P ⊓ (Q ⊓ S)) ⊑T ((P ⊓ Q) ⊓ S))
⊓-assoc-≈T P Q S = ⊓-assoc-⊑-L P Q S , ⊓-assoc-⊑-R P Q S

-------------------------------------------------------------------------------------
-- Prefix:  traces (e ⟶ P) = {⟨⟩} ∪ { ⟨e,x⟩ ∷ t : t ∈ traces (P x) },
-- and prefix is ⊑ᵀ-monotone.
-------------------------------------------------------------------------------------

-- the matching prefix branch fires (no-case discharged by neq refl)
Prefix-cont-just : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
                 → (e : E A) (P : A → PTree E (ExtI E) R) (x : A)
                 → Prefix-cont e P (A , e) x ≡ just (P x)
Prefix-cont-just {A = A} e P x with E-≟ (A , e) (A , e)
... | yes refl = refl
... | no  neq  = ⊥-elim (neq refl)

⟶-trace-nil : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
              {e : E A} {P : A → PTree E (ExtI E) R}
            → traces (Prefix e P) []
⟶-trace-nil = _ , ⟹-refl

-- introduction: do the event e with value x, then any trace of (P x)
⟶-trace-cons : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
               (e : E A) (P : A → PTree E (ExtI E) R) (x : A) {t}
             → traces (P x) t → traces (Prefix e P) (evl (evLabel A e x) ∷ t)
⟶-trace-cons e P x (Px′ , tr) =
  Px′ , ⟹-ev (sVis {at = _ , e} {a = x} refl (Prefix-cont-just e P x)) tr

-- elimination: every trace of (e ⟶ P) is empty or starts with an e-event
⟶-trace-elim : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
               (e : E A) (P : A → PTree E (ExtI E) R) {s}
             → traces (Prefix e P) s
             → (s ≡ []) ⊎ (Σ[ x ∈ A ] Σ[ t ∈ List (Event√ R) ]
                            (s ≡ evl (evLabel A e x) ∷ t × traces (P x) t))
⟶-trace-elim e P (_ , ⟹-refl)              = inj₁ refl
⟶-trace-elim e P (_ , ⟹-τ (sSil ()) _)
⟶-trace-elim e P (_ , ⟹-τ (sTau refl ()) _)
⟶-trace-elim e P (_ , ⟹-ev (sRet ()) _)
⟶-trace-elim {A = A} e P (end , ⟹-ev (sVis {at = at} {a = x} refl br) rest)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = inj₂ (x , _ , refl , end , rest)

-- ⊑ᵀ-monotonicity (and the ⟶₀ corollary)
⟶-mono-⊑ᵀ : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
             (e : E A) {P P′ : A → PTree E (ExtI E) R}
           → (∀ x → P x ⊑T P′ x) → (Prefix e P) ⊑T (Prefix e P′)
⟶-mono-⊑ᵀ e {P} {P′} hyp s tr with ⟶-trace-elim e P′ tr
... | inj₁ refl                  = ⟶-trace-nil
... | inj₂ (x , t , refl , tP′x) = ⟶-trace-cons e P x (hyp x t tP′x)

⟶₀-mono-⊑ᵀ : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
             (e : E A) {Q Q′ : PTree E (ExtI E) R}
           → Q ⊑T Q′ → (Prefix₀ e Q) ⊑T (Prefix₀ e Q′)
⟶₀-mono-⊑ᵀ e q⊑q′ = ⟶-mono-⊑ᵀ e (λ _ → q⊑q′)

-------------------------------------------------------------------------------------
-- Sliding choice:  (P ▷ Q) ⊑T P  — every trace of P is a trace of P ▷ Q.
-- P ▷ Q offers all of P's visible events directly (so an event of P resolves the
-- slide), and mirrors each of P's τ-moves, sliding on as (·▷ Q).
-------------------------------------------------------------------------------------

-- force-equation lemmas: their GOAL mentions `force (P ▷ Q)`, so re-doing the
-- `with PTree.force P` here lets `_▷_` reduce (cf. the original `force-□-*`).
force-▷-ret : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R} {r}
            → PTree.force P ≡ ret r → PTree.force (P ▷ Q) ≡ ret r
force-▷-ret {P = P} eqP with PTree.force P
... | ret _    = case eqP of λ { refl → refl }
... | sil _    = case eqP of λ ()
... | react _ _ = case eqP of λ ()

force-▷-react : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
                 {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                 {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
             → PTree.force P ≡ react v τc
             → PTree.force (P ▷ Q) ≡ react v (▷-slide (react v τc) Q)
force-▷-react {P = P} eqP with PTree.force P
... | react _ _ = case eqP of λ { refl → refl }
... | sil _    = case eqP of λ ()
... | ret _    = case eqP of λ ()

force-▷-sil : ∀ {ℓr} {R : Set ℓr} {P Q P₁ : PTree E (ExtI E) R}
            → PTree.force P ≡ sil P₁
            → PTree.force (P ▷ Q) ≡ react ∅v (▷-slide (sil P₁) Q)
force-▷-sil {P = P} eqP with PTree.force P
... | sil _    = case eqP of λ { refl → refl }
... | ret _    = case eqP of λ ()
... | react _ _ = case eqP of λ ()

-- the τ-branch of the slide fires on P's own τ (tag `fsuc fzero`): `▷-slide` is a
-- top-level function whose body `with`-matches the same `τc … a`, so re-doing the
-- `with` here lets it reduce (cf. the original `merged-branch-eq-*` helpers).
▷-slide-τ-eq : ∀ {ℓr} {R : Set ℓr}
                 {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                 {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                 {Q : PTree E (ExtI E) R}
                 {iₚ : AnyTypes (ExtI E)} {aₚ : proj₁ iₚ} {P₁ : PTree E (ExtI E) R}
             → τc iₚ aₚ ≡ just P₁
             → ▷-slide (react v τc) Q ((Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ))
                                     (lift (fsuc fzero) , aₚ)
               ≡ just (P₁ ▷ Q)
▷-slide-τ-eq {τc = τc} {iₚ = iₚ} {aₚ = aₚ} brP with τc (proj₁ iₚ , proj₂ iₚ) aₚ
... | just _  = case brP of λ { refl → refl }
... | nothing = case brP of λ ()

-- when P offers a visible event (or √), P ▷ Q offers the same event to the same
-- successor (the slide's visible part is exactly P's offers, viewV nP)
▷-ev-L : ∀ {ℓr} {R : Set ℓr} {e} {P P₁ Q : PTree E (ExtI E) R}
       → P ─[ ev e ]─► P₁ → (P ▷ Q) ─[ ev e ]─► P₁
▷-ev-L {P = P} {Q = Q} (sRet eqP)     = sRet (force-▷-ret {P = P} {Q = Q} eqP)
▷-ev-L {P = P} {Q = Q} (sVis eqP brP) = sVis (force-▷-react {P = P} {Q = Q} eqP) brP

-- when P does a τ-move, P ▷ Q does the matching τ-move, sliding on as (·▷ Q)
▷-τ-L : ∀ {ℓr} {R : Set ℓr} {P P₁ Q : PTree E (ExtI E) R}
      → P ─[ τ ]─► P₁ → (P ▷ Q) ─[ τ ]─► (P₁ ▷ Q)
▷-τ-L {P = P} {Q = Q} (sSil eqP) =
  sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
       {a = lift (fsuc fzero) , lift fzero} (force-▷-sil {P = P} {Q = Q} eqP) refl
▷-τ-L {P = P} {Q = Q} (sTau {v = v} {τc = τc} {i = iₚ} {a = aₚ} eqP brP) =
  sTau {i = (Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)}
       {a = lift (fsuc fzero) , aₚ} (force-▷-react {P = P} {Q = Q} eqP)
       (▷-slide-τ-eq {v = v} {τc = τc} {Q = Q} {iₚ = iₚ} {aₚ = aₚ} brP)

-- every trace of P is a trace of P ▷ Q  (recursion is on the big-step, hence total)
⊑ᵀ-▷-L : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) → (P ▷ Q) ⊑T P
⊑ᵀ-▷-L P Q _ (_  , ⟹-refl)        = (P ▷ Q) , ⟹-refl
⊑ᵀ-▷-L P Q s (P′ , ⟹-τ {q = P₁} step rest)
  with ⊑ᵀ-▷-L P₁ Q s (P′ , rest)
... | R′ , rec                     = R′ , ⟹-τ (▷-τ-L step) rec
⊑ᵀ-▷-L P Q _ (P′ , ⟹-ev step rest) = P′ , ⟹-ev (▷-ev-L step) rest
