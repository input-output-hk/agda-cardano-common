{-# OPTIONS --guardedness #-}

-- SPIKE: loop / loop0 / while are ≈-congruences, via iter-cong + a left-congruence
-- for >>= with a PURE-RETURN continuation (κ r rets immediately).  For such κ the
-- ret-boundary is clean — P >>= κ becomes κ r and emits one √ — so no τ*-into-≈
-- composition is needed (that subtlety is what makes the GENERAL >>=-≈-congruence
-- hard; here it's iter-bind-cong minus the loop).
-- No postulates, no NON_TERMINATING.

open import Level using (Level)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Laws.Bisim.LoopCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators   E-≟
open import Semantics.LTS        {E = E} {I = ExtI E}
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
open import CSP.Laws.Bisim.IterCong   E-≟ using (iter-cong; ret-no-τ; sil-no-ev; sil-τ-inv; react-τ-inv)

private
  variable
    ℓr ℓs ℓx : Level
    A : Set ℓ
    R : Set ℓr
    S : Set ℓs
    X : Set ℓx

-------------------------------------------------------------------------------------
-- bind force-eqs / branch-eqs (local)
-------------------------------------------------------------------------------------

fBind-ret : (κ : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R) {r : R}
          → PTree.force P ≡ ret r → PTree.force (P >>= κ) ≡ PTree.force (κ r)
fBind-ret κ P eqP with PTree.force P
... | ret _    = case eqP of λ { refl → refl }
... | sil _    = case eqP of λ ()
... | react _ _ = case eqP of λ ()

fBind-sil : (κ : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R) {c : PTree E (ExtI E) R}
          → PTree.force P ≡ sil c → PTree.force (P >>= κ) ≡ sil (c >>= κ)
fBind-sil κ P eqP with PTree.force P
... | sil _    = case eqP of λ { refl → refl }
... | ret _    = case eqP of λ ()
... | react _ _ = case eqP of λ ()

fBind-react : (κ : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
               {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
           → PTree.force P ≡ react v τc
           → PTree.force (P >>= κ) ≡ react (bindV κ (react v τc)) (bindT κ (react v τc))
fBind-react κ P eqP with PTree.force P
... | react _ _ = case eqP of λ { refl → refl }
... | ret _    = case eqP of λ ()
... | sil _    = case eqP of λ ()

bindT-eq : (κ : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
             {i : AnyTypes (ExtI E)} {a : proj₁ i} {t′ : PTree E (ExtI E) R}
         → viewT nP i a ≡ just t′ → bindT κ nP i a ≡ just (t′ >>= κ)
bindT-eq κ nP {i = i} {a = a} ve with viewT nP i a
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

bindV-eq : (κ : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
             {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) R}
         → viewV nP at a ≡ just t′ → bindV κ nP at a ≡ just (t′ >>= κ)
bindV-eq κ nP {at = at} {a = a} ve with viewV nP at a
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

bindT-elim : (κ : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
               {i : AnyTypes (ExtI E)} {a : proj₁ i} {u : PTree E (ExtI E) S}
           → bindT κ nP i a ≡ just u
           → Σ[ t′ ∈ PTree E (ExtI E) R ] (viewT nP i a ≡ just t′) × (u ≡ t′ >>= κ)
bindT-elim κ nP {i = i} {a = a} eq with viewT nP i a
... | just t′ = t′ , refl , sym (just-injective eq)
... | nothing = case eq of λ ()

bindV-elim : (κ : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
               {at : AnyTypes E} {a : proj₁ at} {u : PTree E (ExtI E) S}
           → bindV κ nP at a ≡ just u
           → Σ[ t′ ∈ PTree E (ExtI E) R ] (viewV nP at a ≡ just t′) × (u ≡ t′ >>= κ)
bindV-elim κ nP {at = at} {a = a} eq with viewV nP at a
... | just t′ = t′ , refl , sym (just-injective eq)
... | nothing = case eq of λ ()

-------------------------------------------------------------------------------------
-- threading lemmas + ≈-reaches-ret (generic)
-------------------------------------------------------------------------------------

bind-τ : (κ : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R) {c : PTree E (ExtI E) R}
       → P ─[ τ ]─► c → (P >>= κ) ─[ τ ]─► (c >>= κ)
bind-τ κ P (sSil eqf)                      = sSil (fBind-sil κ P eqf)
bind-τ κ P (sTau {v = v} {τc = τc} eqf br) = sTau (fBind-react κ P eqf) (bindT-eq κ (react v τc) br)

bind-ev : (κ : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
            {B : Set ℓ} {e : E B} {a : B} {c : PTree E (ExtI E) R}
        → P ─[ ev (evl (evLabel B e a)) ]─► c → (P >>= κ) ─[ ev (evl (evLabel B e a)) ]─► (c >>= κ)
bind-ev κ P (sVis {v = v} {τc = τc} eqf br) = sVis (fBind-react κ P eqf) (bindV-eq κ (react v τc) br)

bind-τ* : (κ : R → PTree E (ExtI E) S) {t c : PTree E (ExtI E) R}
        → t ─[τ*]─► c → (t >>= κ) ─[τ*]─► (c >>= κ)
bind-τ* κ τ*-refl          = τ*-refl
bind-τ* κ (τ*-step st rest) = τ*-step (bind-τ κ _ st) (bind-τ* κ rest)

≈-reaches-ret : {t t′ : PTree E (ExtI E) X} {Y : X}
              → t ≈ t′ → PTree.force t ≡ ret Y
              → Σ[ p′ ∈ PTree E (ExtI E) X ] (t′ ─[τ*]─► p′) × (PTree.force p′ ≡ ret Y)
≈-reaches-ret tt′ eqt with tt′ .Wbisim.fwd .WSimF.on-ev (sRet eqt)
... | _ , wev t′→p′ (sRet fp′) _ , _ = _ , t′→p′ , fp′

-------------------------------------------------------------------------------------
-- >>= with a pure-return continuation is a left ≈-congruence
-------------------------------------------------------------------------------------

module _ (κ : R → PTree E (ExtI E) S)
         (pure : ∀ r → Σ[ s ∈ S ] PTree.force (κ r) ≡ ret s) where

  bindκ-cong : {P P′ : PTree E (ExtI E) R} → P ≈ P′ → (P >>= κ) ≈ (P′ >>= κ)
  bindκ-sim  : {P P′ : PTree E (ExtI E) R} → P ≈ P′ → WSimF (Wbisim S) (P >>= κ) (P′ >>= κ)

  bindκ-cong PP′ .Wbisim.fwd = bindκ-sim PP′
  bindκ-cong PP′ .Wbisim.bwd = bindκ-sim (wbisim-sym PP′)

  bindκ-sim {P = P} {P′ = P′} PP′ .WSimF.on-tau step with PTree.force P in eqP
  ... | ret r = ⊥-elim (ret-no-τ (trans (fBind-ret κ P eqP) (proj₂ (pure r))) step)
  bindκ-sim {P = P} {P′ = P′} PP′ .WSimF.on-tau step | sil c
    with sil-τ-inv (fBind-sil κ P eqP) step | PP′ .Wbisim.fwd .WSimF.on-tau (sSil eqP)
  ...   | refl | c′ , wτ t′→c′ , cc′ = c′ >>= κ , wτ (bind-τ* κ t′→c′) , bindκ-cong cc′
  bindκ-sim {P = P} {P′ = P′} PP′ .WSimF.on-tau step | react v τc
    with react-τ-inv (fBind-react κ P eqP) step
  ...   | i , a , br with bindT-elim κ (react v τc) br
  ...     | t″ , vτ , refl with PP′ .Wbisim.fwd .WSimF.on-tau (sTau eqP vτ)
  ...       | t‴ , wτ t′→t‴ , rel = t‴ >>= κ , wτ (bind-τ* κ t′→t‴) , bindκ-cong rel

  bindκ-sim {P = P} {P′ = P′} PP′ .WSimF.on-ev step with PTree.force P in eqP
  ... | sil c = ⊥-elim (sil-no-ev (fBind-sil κ P eqP) step)
  bindκ-sim {P = P} {P′ = P′} PP′ .WSimF.on-ev step | ret r with pure r
  ... | s , κeq with step
  ...   | sVis eqf _ = ⊥-elim (case trans (sym (trans (fBind-ret κ P eqP) κeq)) eqf of λ ())
  ...   | sRet eqf with trans (sym (trans (fBind-ret κ P eqP) κeq)) eqf | ≈-reaches-ret PP′ eqP
  ...     | refl | p′ , P′→p′ , fp′ =
            deadlock
          , wev (bind-τ* κ P′→p′) (sRet (trans (fBind-ret κ p′ fp′) κeq)) τ*-refl
          , wbisim-refl deadlock
  bindκ-sim {P = P} {P′ = P′} PP′ .WSimF.on-ev step | react v τc with step
  ... | sRet eqf = ⊥-elim (case trans (sym (fBind-react κ P eqP)) eqf of λ ())
  ... | sVis {at = at} {a = a} eqf br with bindV-elim κ (react v τc)
          (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective (trans (sym (fBind-react κ P eqP)) eqf)))) br)
  ...   | t″ , vv , refl with PP′ .Wbisim.fwd .WSimF.on-ev (sVis eqP vv)
  ...     | t‴ , wev t′→p′ p′ev q′→t‴ , rel =
            t‴ >>= κ
          , wev (bind-τ* κ t′→p′) (bind-ev κ _ p′ev) (bind-τ* κ q′→t‴)
          , bindκ-cong rel

-------------------------------------------------------------------------------------
-- loop / loop0 / while are ≈-congruences
-------------------------------------------------------------------------------------

loop-cong : {body body′ : A → PTree E (ExtI E) A}
          → (∀ a → (body a) ≈ (body′ a)) → (∀ a → (loop {R = R} body a) ≈ (loop {R = R} body′ a))
loop-cong {R = R} bb′ a =
  iter-cong (λ a″ → bindκ-cong (λ a′ → Ret (inj₁ a′)) (λ r → inj₁ r , refl) (bb′ a″)) a

loop0-cong : {body body′ : PTree E (ExtI E) (⊤ {ℓ})}
           → body ≈ body′ → (loop0 {R = R} body) ≈ (loop0 {R = R} body′)
loop0-cong bb′ = loop-cong (λ _ → bb′) tt

while-cong : {A : Set ℓ} (cond : A → Bool) {body body′ : A → PTree E (ExtI E) A}
           → (∀ a → (body a) ≈ (body′ a)) → (∀ a → (while cond body a) ≈ (while cond body′ a))
while-cong cond bb′ a =
  iter-cong (λ a″ → bindκ-cong (λ a′ → Ret (if cond a′ then inj₁ a′ else inj₂ a′))
                               (λ r → (if cond r then inj₁ r else inj₂ r) , refl) (bb′ a″)) a
