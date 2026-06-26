{-# OPTIONS --guardedness #-}

-- SPIKE: parallel-composition transition INTRO lemmas on the pure-react layer, for the
-- GENERALISED Par (P : PTree R₁, Q : PTree R₂, joint √ combined by merge : R₁→R₂→R).
-- The reusable operational foundation for Par/⦀ trace reasoning:
--   Par-τ-L / Par-τ-R : each operand's τ is mirrored by the composite;
--   Par-sync          : a shared (in `A`) event fires when BOTH operands offer it.
-- (The full de-interleaving ELIMINATION + Par-mono is the big remaining piece — cf.
--  the original ~500-line AlphaParallel-trace-aux.  Par-comm is FALSE here: ret|ret
--  merges as `merge r₁ r₂`, asymmetric in general.)

open import Level using (Level; Lift; lift)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsParallel {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators          E-≟
open EventSet
open import Semantics.LTS               {E = E} {I = ExtI E}
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)

private
  variable
    ℓ₁ ℓ₂ ℓs : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓs

-- shorthand for the merge parameter (the sync set is now a single `EventSet`)
Mg : Set ℓ₁ → Set ℓ₂ → Set ℓs → Set _
Mg R₁ R₂ R = R₁ → R₂ → R

-------------------------------------------------------------------------------------
-- force-equation lemmas (goal mentions force (Par A merge P Q), so re-doing the
-- `with force P | force Q` reduces it), one per (force P , force Q) shape we need.
-------------------------------------------------------------------------------------

-- P silent, Q done
fPar-sr : (A : EventSet) (merge : Mg R₁ R₂ R)
          {P P' : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {r : R₂}
        → PTree.force P ≡ sil P' → PTree.force Q ≡ ret r
        → PTree.force (Par A merge P Q) ≡ sil (Par A merge P' Q)
fPar-sr A merge {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q
... | sil _    | ret _    = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | sil _    | sil _    = case eqQ of λ ()
... | sil _    | react _ _ = case eqQ of λ ()
... | ret _    | _        = case eqP of λ ()
... | react _ _ | _        = case eqP of λ ()

-- P offering, Q done
fPar-er : (A : EventSet) (merge : Mg R₁ R₂ R)
          {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {r : R₂}
          {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₁))}
          {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₁))}
        → PTree.force P ≡ react vP τcP → PTree.force Q ≡ ret r
        → PTree.force (Par A merge P Q)
          ≡ react (par-hVisL A merge vP Q) (par-hTauL A merge τcP Q)
fPar-er A merge {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q
... | react _ _ | ret _    = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | react _ _ | sil _    = case eqQ of λ ()
... | react _ _ | react _ _ = case eqQ of λ ()
... | ret _    | _        = case eqP of λ ()
... | sil _    | _        = case eqP of λ ()

-- P done, Q silent
fPar-rs : (A : EventSet) (merge : Mg R₁ R₂ R)
          {P : PTree E (ExtI E) R₁} {Q Q' : PTree E (ExtI E) R₂} {r : R₁}
        → PTree.force P ≡ ret r → PTree.force Q ≡ sil Q'
        → PTree.force (Par A merge P Q) ≡ sil (Par A merge P Q')
fPar-rs A merge {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q
... | ret _    | sil _    = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | ret _    | ret _    = case eqQ of λ ()
... | ret _    | react _ _ = case eqQ of λ ()
... | sil _    | _        = case eqP of λ ()
... | react _ _ | _        = case eqP of λ ()

-- P done, Q offering
fPar-re : (A : EventSet) (merge : Mg R₁ R₂ R)
          {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {r : R₁}
          {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₂))}
          {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₂))}
        → PTree.force P ≡ ret r → PTree.force Q ≡ react vQ τcQ
        → PTree.force (Par A merge P Q)
          ≡ react (par-hVisR A merge P vQ) (par-hTauR A merge P τcQ)
fPar-re A merge {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q
... | ret _    | react _ _ = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | ret _    | ret _    = case eqQ of λ ()
... | ret _    | sil _    = case eqQ of λ ()
... | sil _    | _        = case eqP of λ ()
... | react _ _ | _        = case eqP of λ ()

-- neither terminates
fPar-nn : (A : EventSet) (merge : Mg R₁ R₂ R)
          {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
          {nP : NodeKind E (ExtI E) R₁} {nQ : NodeKind E (ExtI E) R₂}
        → PTree.force P ≡ nP → PTree.force Q ≡ nQ → NonRet nP → NonRet nQ
        → PTree.force (Par A merge P Q)
          ≡ react (par-pVis A merge nP nQ P Q) (par-pTau A merge nP nQ P Q)
fPar-nn A merge {P = P} {Q = Q} eqP eqQ ntP ntQ with PTree.force P | PTree.force Q
... | sil _    | sil _    = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | sil _    | react _ _ = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | react _ _ | sil _    = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | react _ _ | react _ _ = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | ret _    | _        = case eqP of λ { refl → ⊥-elim ntP }
... | sil _    | ret _    = case eqQ of λ { refl → ⊥-elim ntQ }
... | react _ _ | ret _    = case eqQ of λ { refl → ⊥-elim ntQ }

-------------------------------------------------------------------------------------
-- branch-equation lemmas for the named continuations
-------------------------------------------------------------------------------------

-- Q done ⇒ P's own τ fires through hTauL (direct, untagged index)
par-hTauL-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                 {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₁))}
                 (Q : PTree E (ExtI E) R₂) {i : AnyTypes (ExtI E)} {a : proj₁ i} {P' : PTree E (ExtI E) R₁}
             → τcP i a ≡ just P' → par-hTauL A merge τcP Q i a ≡ just (Par A merge P' Q)
par-hTauL-eq A merge {τcP = τcP} Q {i = i} {a = a} brP with τcP i a
... | just _  = case brP of λ { refl → refl }
... | nothing = case brP of λ ()

-- P done ⇒ Q's own τ fires through hTauR
par-hTauR-eq : (A : EventSet) (merge : Mg R₁ R₂ R) (P : PTree E (ExtI E) R₁)
                 {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₂))}
                 {i : AnyTypes (ExtI E)} {a : proj₁ i} {Q' : PTree E (ExtI E) R₂}
             → τcQ i a ≡ just Q' → par-hTauR A merge P τcQ i a ≡ just (Par A merge P Q')
par-hTauR-eq A merge P {τcQ = τcQ} {i = i} {a = a} brQ with τcQ i a
... | just _  = case brQ of λ { refl → refl }
... | nothing = case brQ of λ ()

-- both live ⇒ P's τ at tag0 (→ P′ ∥ Q)
par-pTau-tag0-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                     (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                     (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                     {iₚ : AnyTypes (ExtI E)} {aₚ : proj₁ iₚ} {P' : PTree E (ExtI E) R₁}
                 → viewT nP iₚ aₚ ≡ just P'
                 → par-pTau A merge nP nQ P Q
                            ((Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)) (lift fzero , aₚ)
                   ≡ just (Par A merge P' Q)
par-pTau-tag0-eq A merge nP nQ P Q {iₚ = iₚ} {aₚ = aₚ} ve with viewT nP (proj₁ iₚ , proj₂ iₚ) aₚ
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

-- both live ⇒ Q's τ at tag1 (→ P ∥ Q′)
par-pTau-tag1-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                     (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                     (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                     {iₚ : AnyTypes (ExtI E)} {aₚ : proj₁ iₚ} {Q' : PTree E (ExtI E) R₂}
                 → viewT nQ iₚ aₚ ≡ just Q'
                 → par-pTau A merge nP nQ P Q
                            ((Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)) (lift (fsuc fzero) , aₚ)
                   ≡ just (Par A merge P Q')
par-pTau-tag1-eq A merge nP nQ P Q {iₚ = iₚ} {aₚ = aₚ} ve with viewT nQ (proj₁ iₚ , proj₂ iₚ) aₚ
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

-- both live ⇒ a shared (in `A`) event fires when both offer it (→ P′ ∥ Q′)
par-pVis-sync-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                     (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                     (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                     {at : AnyTypes E} {a : proj₁ at}
                     {P' : PTree E (ExtI E) R₁} {Q' : PTree E (ExtI E) R₂}
                 → A .mem at a → viewV nP at a ≡ just P' → viewV nQ at a ≡ just Q'
                 → par-pVis A merge nP nQ P Q at a ≡ just (Par A merge P' Q')
par-pVis-sync-eq A merge nP nQ P Q {at = at} {a = a} csat veP veQ
  with A .dec at a | viewV nP at a | viewV nQ at a
... | yes _   | just _  | just _  = case veP of λ { refl → case veQ of λ { refl → refl } }
... | no  ¬cs | _       | _       = ⊥-elim (¬cs csat)
... | yes _   | nothing | _       = case veP of λ ()
... | yes _   | just _  | nothing = case veQ of λ ()

-------------------------------------------------------------------------------------
-- transition intro lemmas
-------------------------------------------------------------------------------------

-- P's τ is mirrored by Par (→ P′ ∥ Q)
Par-τ-L : (A : EventSet) (merge : Mg R₁ R₂ R)
          (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂) {P' : PTree E (ExtI E) R₁}
        → P ─[ τ ]─► P' → (Par A merge P Q) ─[ τ ]─► (Par A merge P' Q)
Par-τ-L A merge P Q {P'} (sSil eqP) with PTree.force Q in eqQ
... | ret r       = sSil (fPar-sr A merge eqP eqQ)
... | sil Q'      = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                         {a = lift fzero , lift fzero}
                         (fPar-nn A merge eqP eqQ tt tt)
                         (par-pTau-tag0-eq A merge (sil P') (sil Q') P Q
                                           {iₚ = Lift ℓ (Fin 1) , fin} {aₚ = lift fzero} refl)
... | react vQ τcQ = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                         {a = lift fzero , lift fzero}
                         (fPar-nn A merge eqP eqQ tt tt)
                         (par-pTau-tag0-eq A merge (sil P') (react vQ τcQ) P Q
                                           {iₚ = Lift ℓ (Fin 1) , fin} {aₚ = lift fzero} refl)
Par-τ-L A merge P Q {P'} (sTau {v = vP} {τc = τcP} {i = iₚ} {a = aₚ} eqP brP) with PTree.force Q in eqQ
... | ret r       = sTau {i = iₚ} {a = aₚ} (fPar-er A merge eqP eqQ)
                         (par-hTauL-eq A merge {τcP = τcP} Q {i = iₚ} {a = aₚ} brP)
... | sil Q'      = sTau {i = (Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)}
                         {a = lift fzero , aₚ} (fPar-nn A merge eqP eqQ tt tt)
                         (par-pTau-tag0-eq A merge (react vP τcP) (sil Q') P Q {iₚ = iₚ} {aₚ = aₚ} brP)
... | react vQ τcQ = sTau {i = (Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)}
                         {a = lift fzero , aₚ} (fPar-nn A merge eqP eqQ tt tt)
                         (par-pTau-tag0-eq A merge (react vP τcP) (react vQ τcQ) P Q {iₚ = iₚ} {aₚ = aₚ} brP)

-- Q's τ is mirrored by Par (→ P ∥ Q′)
Par-τ-R : (A : EventSet) (merge : Mg R₁ R₂ R)
          (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂) {Q' : PTree E (ExtI E) R₂}
        → Q ─[ τ ]─► Q' → (Par A merge P Q) ─[ τ ]─► (Par A merge P Q')
Par-τ-R A merge P Q {Q'} (sSil eqQ) with PTree.force P in eqP
... | ret r       = sSil (fPar-rs A merge eqP eqQ)
... | sil P'      = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                         {a = lift (fsuc fzero) , lift fzero}
                         (fPar-nn A merge eqP eqQ tt tt)
                         (par-pTau-tag1-eq A merge (sil P') (sil Q') P Q
                                           {iₚ = Lift ℓ (Fin 1) , fin} {aₚ = lift fzero} refl)
... | react vP τcP = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                         {a = lift (fsuc fzero) , lift fzero}
                         (fPar-nn A merge eqP eqQ tt tt)
                         (par-pTau-tag1-eq A merge (react vP τcP) (sil Q') P Q
                                           {iₚ = Lift ℓ (Fin 1) , fin} {aₚ = lift fzero} refl)
Par-τ-R A merge P Q {Q'} (sTau {v = vQ} {τc = τcQ} {i = iₚ} {a = aₚ} eqQ brQ) with PTree.force P in eqP
... | ret r       = sTau {i = iₚ} {a = aₚ} (fPar-re A merge eqP eqQ)
                         (par-hTauR-eq A merge P {τcQ = τcQ} {i = iₚ} {a = aₚ} brQ)
... | sil P'      = sTau {i = (Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)}
                         {a = lift (fsuc fzero) , aₚ} (fPar-nn A merge eqP eqQ tt tt)
                         (par-pTau-tag1-eq A merge (sil P') (react vQ τcQ) P Q {iₚ = iₚ} {aₚ = aₚ} brQ)
... | react vP τcP = sTau {i = (Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)}
                         {a = lift (fsuc fzero) , aₚ} (fPar-nn A merge eqP eqQ tt tt)
                         (par-pTau-tag1-eq A merge (react vP τcP) (react vQ τcQ) P Q {iₚ = iₚ} {aₚ = aₚ} brQ)

-- SOLO (non-sync) visible step, L: P offers, Q does NOT, event ∉ A  (→ P′ ∥ Q)
-- via the both-live combinator `par-pVis`.  Consumes `viewV nQ at a ≡ nothing` as a
-- hypothesis; does NOT force Q (nQ is the abstract NodeKind given to par-pVis).
par-pVis-soloL-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                      (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                      (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                      {at : AnyTypes E} {a : proj₁ at} {P' : PTree E (ExtI E) R₁}
                  → ¬ A .mem at a → viewV nP at a ≡ just P' → viewV nQ at a ≡ nothing
                  → par-pVis A merge nP nQ P Q at a ≡ just (Par A merge P' Q)
par-pVis-soloL-eq A merge nP nQ P Q {at = at} {a = a} ¬cs veP veQ
  with A .dec at a | viewV nP at a | viewV nQ at a
... | yes cs  | _       | _       = ⊥-elim (¬cs cs)
... | no  _   | just _  | nothing = case veP of λ { refl → refl }
... | no  _   | just _  | just _  = case veQ of λ ()
... | no  _   | nothing | _       = case veP of λ ()

-- SOLO visible step via the `par-hVisL` combinator (Q terminated, P live).
-- Consumes ¬(e ∈ A); does NOT use any property of Q's offer map.
par-hVisL-soloL-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                       {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₁))}
                       (Q : PTree E (ExtI E) R₂)
                       {at : AnyTypes E} {a : proj₁ at} {P' : PTree E (ExtI E) R₁}
                   → ¬ A .mem at a → vP at a ≡ just P'
                   → par-hVisL A merge vP Q at a ≡ just (Par A merge P' Q)
par-hVisL-soloL-eq A merge {vP = vP} Q {at = at} {a = a} ¬cs veP
  with A .dec at a
... | yes cs = ⊥-elim (¬cs cs)
... | no  _  with vP at a
...   | just _  = case veP of λ { refl → refl }
...   | nothing = case veP of λ ()

-- SOLO visible step via `par-pVis`, R side: Q offers, P does NOT, event ∉ A  (→ P ∥ Q′)
par-pVis-soloR-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                      (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                      (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                      {at : AnyTypes E} {a : proj₁ at} {Q' : PTree E (ExtI E) R₂}
                  → ¬ A .mem at a → viewV nP at a ≡ nothing → viewV nQ at a ≡ just Q'
                  → par-pVis A merge nP nQ P Q at a ≡ just (Par A merge P Q')
par-pVis-soloR-eq A merge nP nQ P Q {at = at} {a = a} ¬cs veP veQ
  with A .dec at a | viewV nP at a | viewV nQ at a
... | yes cs  | _       | _       = ⊥-elim (¬cs cs)
... | no  _   | nothing | just _  = case veQ of λ { refl → refl }
... | no  _   | just _  | just _  = case veP of λ ()
... | no  _   | just _  | nothing = case veP of λ ()
... | no  _   | nothing | nothing = case veQ of λ ()

-- SOLO visible step via `par-hVisR` combinator (P terminated, Q live).
par-hVisR-soloR-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                       (P : PTree E (ExtI E) R₁)
                       {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₂))}
                       {at : AnyTypes E} {a : proj₁ at} {Q' : PTree E (ExtI E) R₂}
                   → ¬ A .mem at a → vQ at a ≡ just Q'
                   → par-hVisR A merge P vQ at a ≡ just (Par A merge P Q')
par-hVisR-soloR-eq A merge P {vQ = vQ} {at = at} {a = a} ¬cs veQ
  with A .dec at a
... | yes cs = ⊥-elim (¬cs cs)
... | no  _  with vQ at a
...   | just _  = case veQ of λ { refl → refl }
...   | nothing = case veQ of λ ()

-- a shared (in `A`) event: both operands offer it, the composite synchronises (→ P′ ∥ Q′)
Par-sync : (A : EventSet) (merge : Mg R₁ R₂ R)
           (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
           {X : Set ℓ} {e : E X} {a : X} {P' : PTree E (ExtI E) R₁} {Q' : PTree E (ExtI E) R₂}
         → A .mem (X , e) a
         → P ─[ ev (evl (evLabel X e a)) ]─► P'
         → Q ─[ ev (evl (evLabel X e a)) ]─► Q'
         → (Par A merge P Q) ─[ ev (evl (evLabel X e a)) ]─► (Par A merge P' Q')
Par-sync A merge P Q csat (sVis {v = vP} {τc = τcP} {at = at} {a = a} eqP brP)
                               (sVis {v = vQ} {τc = τcQ} eqQ brQ) =
  sVis (fPar-nn A merge eqP eqQ tt tt)
       (par-pVis-sync-eq A merge (react vP τcP) (react vQ τcQ) P Q csat brP brQ)

-------------------------------------------------------------------------------------
-- SOLO (non-synchronised) visible intro: one operand's step lifts past an idle
-- operand, taking the idle operand's NON-OFFER as an explicit hypothesis.
-- The proof forces Q (it cases on PTree.force Q) but APPLICATIONS of the proven
-- lemma do NOT — the non-offer hypothesis `viewV (force Q) at a ≡ nothing` is
-- enough, so Q may stay abstract at use sites.
-------------------------------------------------------------------------------------

-- P does a non-sync visible step; Q is idle (does not offer that event)  (→ P′ ∥ Q)
Par-soloL : (A : EventSet) (merge : Mg R₁ R₂ R)
            (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
            {X : Set ℓ} {e : E X} {a : X} {P' : PTree E (ExtI E) R₁}
          → ¬ A .mem (X , e) a
          → P ─[ ev (evl (evLabel X e a)) ]─► P'
          → viewV (PTree.force Q) (X , e) a ≡ nothing
          → (Par A merge P Q) ─[ ev (evl (evLabel X e a)) ]─► (Par A merge P' Q)
Par-soloL A merge P Q ¬cs (sVis {v = vP} {τc = τcP} eqP brP) nq
  with PTree.force Q in eqQ
... | ret r        = sVis (fPar-er A merge eqP eqQ)
                          (par-hVisL-soloL-eq A merge {vP = vP} Q ¬cs brP)
... | sil Q'       = sVis (fPar-nn A merge eqP eqQ tt tt)
                          (par-pVis-soloL-eq A merge (react vP τcP) (sil Q') P Q ¬cs brP nq)
... | react vQ τcQ = sVis (fPar-nn A merge eqP eqQ tt tt)
                          (par-pVis-soloL-eq A merge (react vP τcP) (react vQ τcQ) P Q ¬cs brP nq)

-- Mirror: Q does a non-sync visible step; P is idle  (→ P ∥ Q′)
Par-soloR : (A : EventSet) (merge : Mg R₁ R₂ R)
            (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
            {X : Set ℓ} {e : E X} {a : X} {Q' : PTree E (ExtI E) R₂}
          → ¬ A .mem (X , e) a
          → Q ─[ ev (evl (evLabel X e a)) ]─► Q'
          → viewV (PTree.force P) (X , e) a ≡ nothing
          → (Par A merge P Q) ─[ ev (evl (evLabel X e a)) ]─► (Par A merge P Q')
Par-soloR A merge P Q ¬cs (sVis {v = vQ} {τc = τcQ} eqQ brQ) np
  with PTree.force P in eqP
... | ret r        = sVis (fPar-re A merge eqP eqQ)
                          (par-hVisR-soloR-eq A merge P {vQ = vQ} ¬cs brQ)
... | sil P'       = sVis (fPar-nn A merge eqP eqQ tt tt)
                          (par-pVis-soloR-eq A merge (sil P') (react vQ τcQ) P Q ¬cs np brQ)
... | react vP τcP = sVis (fPar-nn A merge eqP eqQ tt tt)
                          (par-pVis-soloR-eq A merge (react vP τcP) (react vQ τcQ) P Q ¬cs np brQ)

-------------------------------------------------------------------------------------
-- VALIDATION: applying Par-soloL / Par-soloR with an ABSTRACT (un-forced) idle operand.
-- These typecheck only if the proven lemmas need NO reduction of `force Q` / `force P`.
-------------------------------------------------------------------------------------

_test-soloL : (A : EventSet) (merge : Mg R₁ R₂ R)
              (P P' : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
              {X : Set ℓ} {e : E X} {a : X}
            → ¬ A .mem (X , e) a
            → P ─[ ev (evl (evLabel X e a)) ]─► P'
            → viewV (PTree.force Q) (X , e) a ≡ nothing
            → (Par A merge P Q) ─[ ev (evl (evLabel X e a)) ]─► (Par A merge P' Q)
_test-soloL A merge P P' Q ¬cs st nq = Par-soloL A merge P Q ¬cs st nq

_test-soloR : (A : EventSet) (merge : Mg R₁ R₂ R)
              (P : PTree E (ExtI E) R₁) (Q Q' : PTree E (ExtI E) R₂)
              {X : Set ℓ} {e : E X} {a : X}
            → ¬ A .mem (X , e) a
            → Q ─[ ev (evl (evLabel X e a)) ]─► Q'
            → viewV (PTree.force P) (X , e) a ≡ nothing
            → (Par A merge P Q) ─[ ev (evl (evLabel X e a)) ]─► (Par A merge P Q')
_test-soloR A merge P Q Q' ¬cs st np = Par-soloR A merge P Q ¬cs st np
