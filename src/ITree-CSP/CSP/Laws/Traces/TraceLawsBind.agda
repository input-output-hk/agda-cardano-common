{-# OPTIONS --guardedness #-}

-- SPIKE: sequential composition (>>= / >>) is ⊑ᵀ-monotone in its CONTINUATION.
--   >>=-mono-k : (∀ r → k r ⊑T k′ r) → (P >>= k) ⊑T (P >>= k′)
--   >>-mono-R  : Q ⊑T Q′ → (P >> Q) ⊑T (P >> Q′)
-- Proof is a simulation on the big-step of P >>= k′: while P is live (sil/react) each
-- step is mirrored; when P terminates (force P ≡ ret r) the composite IS k′ r (force-
-- equal), so the rest is transported through `force-≡→traces-⊆` and the hypothesis at r.
-- (Left-argument mono `>>-mono-L` needs the de-bind decomposition; not done here.)
-- No postulates, no NON_TERMINATING.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsBind {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators               E-≟
open import Semantics.LTS                    {E = E} {I = ExtI E}
open import Semantics.Failures               {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_; ⊑T-trans)
open import CSP.Laws.Traces.TraceLawsGuard         E-≟ using (force-≡→traces-⊆)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (react-τ-inv)
open import CSP.Laws.Traces.TraceLawsParallelElim  E-≟ using (sil-τ-inv)

private
  variable
    ℓr ℓs : Level
    R : Set ℓr
    S : Set ℓs

-------------------------------------------------------------------------------------
-- force-equation lemmas for >>=
-------------------------------------------------------------------------------------

fBind-ret : (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R) {r : R}
          → PTree.force P ≡ ret r → PTree.force (P >>= k) ≡ PTree.force (k r)
fBind-ret k P eqP with PTree.force P
... | ret _    = case eqP of λ { refl → refl }
... | sil _    = case eqP of λ ()
... | react _ _ = case eqP of λ ()

fBind-sil : (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R) {c : PTree E (ExtI E) R}
          → PTree.force P ≡ sil c → PTree.force (P >>= k) ≡ sil (c >>= k)
fBind-sil k P eqP with PTree.force P
... | sil _    = case eqP of λ { refl → refl }
... | ret _    = case eqP of λ ()
... | react _ _ = case eqP of λ ()

fBind-react : (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
               {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
           → PTree.force P ≡ react v τc
           → PTree.force (P >>= k) ≡ react (bindV k (react v τc)) (bindT k (react v τc))
fBind-react k P eqP with PTree.force P
... | react _ _ = case eqP of λ { refl → refl }
... | ret _    = case eqP of λ ()
... | sil _    = case eqP of λ ()

-------------------------------------------------------------------------------------
-- branch-equation lemmas for the lifted bind continuations
-------------------------------------------------------------------------------------

bindT-eq : (k : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
             {i : AnyTypes (ExtI E)} {a : proj₁ i} {t : PTree E (ExtI E) R}
         → viewT nP i a ≡ just t → bindT k nP i a ≡ just (t >>= k)
bindT-eq k nP {i = i} {a = a} ve with viewT nP i a
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

bindT-elim : (k : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
               {i : AnyTypes (ExtI E)} {a : proj₁ i} {u : PTree E (ExtI E) S}
           → bindT k nP i a ≡ just u
           → Σ[ t ∈ PTree E (ExtI E) R ] (viewT nP i a ≡ just t) × (u ≡ t >>= k)
bindT-elim k nP {i = i} {a = a} eq with viewT nP i a
... | just t  = t , refl , sym (just-injective eq)
... | nothing = case eq of λ ()

bindV-eq : (k : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
             {at : AnyTypes E} {a : proj₁ at} {t : PTree E (ExtI E) R}
         → viewV nP at a ≡ just t → bindV k nP at a ≡ just (t >>= k)
bindV-eq k nP {at = at} {a = a} ve with viewV nP at a
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

bindV-elim : (k : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
               {at : AnyTypes E} {a : proj₁ at} {u : PTree E (ExtI E) S}
           → bindV k nP at a ≡ just u
           → Σ[ t ∈ PTree E (ExtI E) R ] (viewV nP at a ≡ just t) × (u ≡ t >>= k)
bindV-elim k nP {at = at} {a = a} eq with viewV nP at a
... | just t  = t , refl , sym (just-injective eq)
... | nothing = case eq of λ ()

-- a node forced to sil makes no visible/√ step
sil-no-ev : {t c u : PTree E (ExtI E) S} {e : Event√ S}
          → PTree.force t ≡ sil c → t ─[ ev e ]─► u → ⊥
sil-no-ev sile (sRet eqf)   = case trans (sym sile) eqf of λ ()
sil-no-ev sile (sVis eqf _) = case trans (sym sile) eqf of λ ()

-------------------------------------------------------------------------------------
-- continuation-monotonicity, by simulation on the big-step of P >>= k′
-------------------------------------------------------------------------------------

bind-mono-k-aux : (k k′ : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
                → (∀ r → (k r) ⊑T (k′ r))
                → {s : List (Event√ S)} {R' : PTree E (ExtI E) S}
                → (P >>= k′) ⟹⟨ s ⟩ R' → traces (P >>= k) s
bind-mono-k-aux k k′ P hyp bs with PTree.force P in eqP
-- P terminated: P >>= k′ IS k′ r — transport the rest through the hypothesis at r
... | ret r = force-≡→traces-⊆ (sym (fBind-ret k P eqP))
                (hyp r _ (force-≡→traces-⊆ (fBind-ret k′ P eqP) (_ , bs)))
-- P does its own τ (sil)
... | sil c with bs
...   | ⟹-refl        = (P >>= k) , ⟹-refl
...   | ⟹-ev step rest = ⊥-elim (sil-no-ev (fBind-sil k′ P eqP) step)
...   | ⟹-τ step rest with sil-τ-inv (fBind-sil k′ P eqP) step
...     | refl with bind-mono-k-aux k k′ c hyp rest
...       | Rt , bs' = Rt , ⟹-τ (sSil (fBind-sil k P eqP)) bs'
-- P offers / does its own τ at an react node
bind-mono-k-aux k k′ P hyp bs | react v τc with bs
... | ⟹-refl = (P >>= k) , ⟹-refl
... | ⟹-τ step rest with react-τ-inv (fBind-react k′ P eqP) step
...   | i , a , br with bindT-elim k′ (react v τc) br
...     | t , vτ , refl with bind-mono-k-aux k k′ t hyp rest
...       | Rt , bs' = Rt , ⟹-τ (sTau (fBind-react k P eqP) (bindT-eq k (react v τc) vτ)) bs'
bind-mono-k-aux k k′ P hyp bs | react v τc | ⟹-ev (sRet eqf) rest =
  case trans (sym (fBind-react k′ P eqP)) eqf of λ ()
bind-mono-k-aux k k′ P hyp bs | react v τc | ⟹-ev (sVis {at = at} {a = a} eqf br) rest
  with bindV-elim k′ (react v τc)
         (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective (trans (sym (fBind-react k′ P eqP)) eqf)))) br)
... | t , vv , refl with bind-mono-k-aux k k′ t hyp rest
...   | Rt , bs' = Rt , ⟹-ev (sVis (fBind-react k P eqP) (bindV-eq k (react v τc) vv)) bs'

-------------------------------------------------------------------------------------
-- the laws
-------------------------------------------------------------------------------------

>>=-mono-k : {k k′ : R → PTree E (ExtI E) S} (P : PTree E (ExtI E) R)
           → (∀ r → (k r) ⊑T (k′ r)) → (P >>= k) ⊑T (P >>= k′)
>>=-mono-k {k = k} {k′ = k′} P hyp s (_ , bs) = bind-mono-k-aux k k′ P hyp bs

>>-mono-R : (P : PTree E (ExtI E) R) {Q Q′ : PTree E (ExtI E) S}
          → Q ⊑T Q′ → (P >> Q) ⊑T (P >> Q′)
>>-mono-R P q⊑ = >>=-mono-k P (λ _ → q⊑)

-------------------------------------------------------------------------------------
-- LEFT-argument monotonicity:  P ⊑T P′ → (P >>= k) ⊑T (P′ >>= k)
-- De-bind: a trace of P′ >>= k is P′'s visible (evl-only) trace while P′ is live,
-- optionally followed — once P′ terminates at r — by a trace of k r.
-------------------------------------------------------------------------------------

-- single-step bind intros (P's own τ / visible event propagate to P >>= k)
bind-τ : (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R) {t : PTree E (ExtI E) R}
       → P ─[ τ ]─► t → (P >>= k) ─[ τ ]─► (t >>= k)
bind-τ k P (sSil eqf)                       = sSil (fBind-sil k P eqf)
bind-τ k P (sTau {v = v} {τc = τc} eqf br)  = sTau (fBind-react k P eqf) (bindT-eq k (react v τc) br)

bind-ev : (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
            {A : Set ℓ} {e : E A} {a : A} {t : PTree E (ExtI E) R}
        → P ─[ ev (evl (evLabel A e a)) ]─► t → (P >>= k) ─[ ev (evl (evLabel A e a)) ]─► (t >>= k)
bind-ev k P (sVis {v = v} {τc = τc} eqf br) = sVis (fBind-react k P eqf) (bindV-eq k (react v τc) br)

-- two traces (over Event√ R / Event√ S) made of the SAME visible events, no √
data EvlOnly {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
     : List (Event√ R) → List (Event√ S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr ⊔ ℓs) where
  enil  : EvlOnly [] []
  econs : ∀ {A : Set ℓ} {e : E A} {a : A} {sR sS}
        → EvlOnly sR sS → EvlOnly (evl (evLabel A e a) ∷ sR) (evl (evLabel A e a) ∷ sS)

-- the de-bind decomposition of a trace of P′ >>= k
data BindSplit {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
       (P′ : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
       (s : List (Event√ S)) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr ⊔ ℓs) where
  bs-live : ∀ {sR P″} → P′ ⟹⟨ sR ⟩ P″ → EvlOnly sR s → BindSplit P′ k s
  bs-term : ∀ {sR P″ r sS s_k} → P′ ⟹⟨ sR ⟩ P″ → PTree.force P″ ≡ ret r
          → EvlOnly sR sS → traces (k r) s_k → s ≡ sS ++ s_k → BindSplit P′ k s

bind-elim-aux : (P′ : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                {s : List (Event√ S)} {R' : PTree E (ExtI E) S}
              → (P′ >>= k) ⟹⟨ s ⟩ R' → BindSplit P′ k s
bind-elim-aux P′ k bs with PTree.force P′ in eqP
... | ret r = bs-term ⟹-refl eqP enil (force-≡→traces-⊆ (fBind-ret k P′ eqP) (_ , bs)) refl
... | sil c with bs
...   | ⟹-refl        = bs-live ⟹-refl enil
...   | ⟹-ev step rest = ⊥-elim (sil-no-ev (fBind-sil k P′ eqP) step)
...   | ⟹-τ step rest with sil-τ-inv (fBind-sil k P′ eqP) step
...     | refl with bind-elim-aux c k rest
...       | bs-live c⟹ eo            = bs-live (⟹-τ (sSil eqP) c⟹) eo
...       | bs-term c⟹ fr eo kt seq  = bs-term (⟹-τ (sSil eqP) c⟹) fr eo kt seq
bind-elim-aux P′ k bs | react v τc with bs
... | ⟹-refl = bs-live ⟹-refl enil
... | ⟹-ev (sRet eqf) rest = case trans (sym (fBind-react k P′ eqP)) eqf of λ ()
... | ⟹-ev (sVis {at = at} {a = a} eqf br) rest
      with bindV-elim k (react v τc)
             (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective (trans (sym (fBind-react k P′ eqP)) eqf)))) br)
...   | t , vv , refl with bind-elim-aux t k rest
...     | bs-live t⟹ eo           = bs-live (⟹-ev (sVis eqP vv) t⟹) (econs eo)
...     | bs-term t⟹ fr eo kt seq = bs-term (⟹-ev (sVis eqP vv) t⟹) fr (econs eo) kt (cong (_ ∷_) seq)
bind-elim-aux P′ k bs | react v τc | ⟹-τ step rest with react-τ-inv (fBind-react k P′ eqP) step
...   | i , a , br with bindT-elim k (react v τc) br
...     | t , vτ , refl with bind-elim-aux t k rest
...       | bs-live t⟹ eo           = bs-live (⟹-τ (sTau eqP vτ) t⟹) eo
...       | bs-term t⟹ fr eo kt seq = bs-term (⟹-τ (sTau eqP vτ) t⟹) fr eo kt seq

-- big-step lemmas at the termination boundary (append / split a trailing √)
⟹-append-√ : {P P″ : PTree E (ExtI E) R} {sR : List (Event√ R)} {r : R}
           → P ⟹⟨ sR ⟩ P″ → PTree.force P″ ≡ ret r → P ⟹⟨ sR ++ (√ r ∷ []) ⟩ deadlock
⟹-append-√ ⟹-refl        fr = ⟹-ev (sRet fr) ⟹-refl
⟹-append-√ (⟹-τ st rest)  fr = ⟹-τ  st (⟹-append-√ rest fr)
⟹-append-√ (⟹-ev st rest) fr = ⟹-ev st (⟹-append-√ rest fr)

⟹-split-√ : (P : PTree E (ExtI E) R) (sR : List (Event√ R)) {r : R} {Rt : PTree E (ExtI E) R}
          → P ⟹⟨ sR ++ (√ r ∷ []) ⟩ Rt
          → Σ[ P‴ ∈ PTree E (ExtI E) R ] (P ⟹⟨ sR ⟩ P‴) × (PTree.force P‴ ≡ ret r)
⟹-split-√ P [] (⟹-τ st rest) with ⟹-split-√ _ [] rest
... | P‴ , w , fr = P‴ , ⟹-τ st w , fr
⟹-split-√ P [] (⟹-ev (sRet eqf) rest) = P , ⟹-refl , eqf
⟹-split-√ P (e₀ ∷ sR') (⟹-τ st rest) with ⟹-split-√ _ (e₀ ∷ sR') rest
... | P‴ , w , fr = P‴ , ⟹-τ st w , fr
⟹-split-√ P (e₀ ∷ sR') (⟹-ev st rest) with ⟹-split-√ _ sR' rest
... | P‴ , w , fr = P‴ , ⟹-ev st w , fr

-- re-injection: P's live evl-trace, then optionally k r
bind-intro-live : (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
                    {sR : List (Event√ R)} {P″ : PTree E (ExtI E) R} {s : List (Event√ S)}
                → P ⟹⟨ sR ⟩ P″ → EvlOnly sR s → traces (P >>= k) s
bind-intro-live k P ⟹-refl enil = (P >>= k) , ⟹-refl
bind-intro-live k P (⟹-τ Pτ rest) eo with bind-intro-live k _ rest eo
... | Rt , bs' = Rt , ⟹-τ (bind-τ k P Pτ) bs'
bind-intro-live k P (⟹-ev Pev rest) (econs eo) with bind-intro-live k _ rest eo
... | Rt , bs' = Rt , ⟹-ev (bind-ev k P Pev) bs'

bind-intro-term : (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
                    {sR : List (Event√ R)} {P″ : PTree E (ExtI E) R} {r : R}
                    {sS : List (Event√ S)} {s_k : List (Event√ S)} {s : List (Event√ S)}
                → P ⟹⟨ sR ⟩ P″ → PTree.force P″ ≡ ret r → EvlOnly sR sS
                → traces (k r) s_k → s ≡ sS ++ s_k → traces (P >>= k) s
bind-intro-term k P ⟹-refl fr enil kt refl = force-≡→traces-⊆ (sym (fBind-ret k P fr)) kt
bind-intro-term k P (⟹-τ Pτ rest) fr eo kt seq with bind-intro-term k _ rest fr eo kt seq
... | Rt , bs' = Rt , ⟹-τ (bind-τ k P Pτ) bs'
bind-intro-term k P (⟹-ev Pev rest) fr (econs eo) kt refl with bind-intro-term k _ rest fr eo kt refl
... | Rt , bs' = Rt , ⟹-ev (bind-ev k P Pev) bs'

>>=-mono-L : {P P′ : PTree E (ExtI E) R} (k : R → PTree E (ExtI E) S)
           → P ⊑T P′ → (P >>= k) ⊑T (P′ >>= k)
>>=-mono-L {P = P} {P′ = P′} k p⊑ s (_ , bs) with bind-elim-aux P′ k bs
... | bs-live P′⟹ eo with p⊑ _ (_ , P′⟹)
...   | _ , P⟹ = bind-intro-live k P P⟹ eo
>>=-mono-L {P = P} {P′ = P′} k p⊑ s (_ , bs) | bs-term {sR = sR} {r = r} P′⟹ fr eo kt seq
  with p⊑ (sR ++ (√ r ∷ [])) (_ , ⟹-append-√ P′⟹ fr)
... | _ , P⟹√ with ⟹-split-√ P sR P⟹√
...   | _ , P⟹ , fr′ = bind-intro-term k P P⟹ fr′ eo kt seq

>>-mono-L : {P P′ : PTree E (ExtI E) R} (Q : PTree E (ExtI E) S)
          → P ⊑T P′ → (P >> Q) ⊑T (P′ >> Q)
>>-mono-L Q p⊑ = >>=-mono-L (λ _ → Q) p⊑

-------------------------------------------------------------------------------------
-- Kleisli composition is ⊑ᵀ-monotone (pointwise, in both arrows)
-------------------------------------------------------------------------------------

>=>-mono : ∀ {ℓt} {T : Set ℓt}
             {f f′ : R → PTree E (ExtI E) S} {g g′ : S → PTree E (ExtI E) T}
         → (∀ x → (f x) ⊑T (f′ x)) → (∀ y → (g y) ⊑T (g′ y))
         → (∀ x → ((f >=> g) x) ⊑T ((f′ >=> g′) x))
>=>-mono {f = f} {f′ = f′} {g = g} {g′ = g′} fhyp ghyp x =
  ⊑T-trans (>>=-mono-L g (fhyp x)) (>>=-mono-k (f′ x) ghyp)
