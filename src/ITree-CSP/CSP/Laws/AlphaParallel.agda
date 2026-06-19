{-# OPTIONS --guardedness #-}

open import Level using (_⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _++_; _∷_; []; [_]; map)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; subst)

open import Process_Trees
open import Semantics.LTS
open import Semantics.Failures using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import Semantics.Deadlock
open import Semantics.Refusals

module CSP.Laws.AlphaParallel
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open PTree
open Event

import CSP.Operators {ℓ} {ℓe} {E} E-≟ as CSPOps
open CSPOps using
  ( EventSet
  ; _⟦_∥_⟧_
  ; αpar-pTau; αpar-hTauR; αpar-hTauL
  ; αpar-sync-step; αpar-soloL-step; αpar-soloR-step
  ; Stop
  )
open EventSet

-------------------------------------------------------------------------------------
-- Synchronisation merge predicate (two alphabets, dual guards).
-- An event routes by alphabet membership:
--   sync-l    : event in A only      → P performs it solo
--   sync-r    : event in B only      → Q performs it solo
--   sync-both : event in both A and B → P and Q synchronise

data AlphaSync {ℓi} {I : Set ℓ → Set ℓi} (A B : EventSet)
  : List (Event {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I}) → List (Event {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I}) → List (Event {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I})
  → Set (lsuc ℓ ⊔ ℓe) where
  sync-nil  : AlphaSync A B [] [] []
  sync-l    : ∀ {sP sQ s e}
            →   A .mem (Event.A e , Event.e e) (Event.a e) → ¬ B .mem (Event.A e , Event.e e) (Event.a e)
            → AlphaSync A B sP sQ s → AlphaSync A B (e ∷ sP) sQ (e ∷ s)
  sync-r    : ∀ {sP sQ s e}
            → ¬ A .mem (Event.A e , Event.e e) (Event.a e) →   B .mem (Event.A e , Event.e e) (Event.a e)
            → AlphaSync A B sP sQ s → AlphaSync A B sP (e ∷ sQ) (e ∷ s)
  sync-both : ∀ {sP sQ s e}
            →   A .mem (Event.A e , Event.e e) (Event.a e) →   B .mem (Event.A e , Event.e e) (Event.a e)
            → AlphaSync A B sP sQ s → AlphaSync A B (e ∷ sP) (e ∷ sQ) (e ∷ s)

-- Splitting witness for traces of the binary alphabetised parallel.
data AlphaSyncSplit {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (A B : EventSet) (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
  : List (Event√ {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} (R × S))
  → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where
  in-progress : ∀ {sP sQ s : List (Event {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I})}
              → AlphaSync {I = I} A B sP sQ s
              → traces P (map evl sP) → traces Q (map evl sQ)
              → AlphaSyncSplit A B P Q (map evl s)
  done : ∀ {sP sQ s : List (Event {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I})} {r : R} {q : S}
       → AlphaSync {I = I} A B sP sQ s
       → traces P (map evl sP ++ [ √ r ]) → traces Q (map evl sQ ++ [ √ q ])
       → AlphaSyncSplit A B P Q (map evl s ++ [ √ (r , q) ])

-------------------------------------------------------------------------------------
-- Refusal-composition (IsStuck) for binary alphabetised parallel.
--
-- When both operands are `react`-headed AND stable (their τ-maps are everywhere
-- `nothing`) and *every* event (at , a) is "blocked" — the routing offer on the
-- side(s) the alphabets require is `nothing` — the composite can fire neither an
-- event nor a τ, hence `IsStuck`.  This is the key tool for deadlock proofs.
--
-- NOTE (react port): the legacy hypothesis was `P .force ≡ vis fP`, where a `vis`
-- node carried no τ-branch.  Under the fused `react` node a node CAN offer τ even
-- while react-headed, so to preserve the legacy fact ("no move at all is possible")
-- we additionally require the operands to be STABLE (`τcP`/`τcQ` everywhere `nothing`).
-- For `vis`-derived operands (Stop, prefix-guarded choices) this holds definitionally.

-- The routing fails for event (at , a): the composite cannot fire it.
Blocked : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    (A B : EventSet)
    (fP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R)))
    (fQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) S)))
    (at : AnyTypes E) (a : proj₁ at) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs)
Blocked {ℓi = ℓi} {ℓr = ℓr} {ℓs = ℓs} A B fP fQ at a =
  case (A .dec at a , B .dec at a) of λ where
    -- both alphabets claim e: blocked iff either side refuses the offer
    (yes _ , yes _) → Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs)
                          ((fP at a ≡ nothing) ⊎ (fQ at a ≡ nothing))
    -- only A claims e: blocked iff P refuses
    (yes _ , no  _) → Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) (fP at a ≡ nothing)
    -- only B claims e: blocked iff Q refuses
    (no  _ , yes _) → Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) (fQ at a ≡ nothing)
    -- e in neither alphabet: always refused (vacuously blocked)
    (no  _ , no  _) → ⊤ {lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs}

αpar-IsStuck : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A B : EventSet}
    {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
    {vP τcP vQ τcQ}
  → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ
  → (∀ i a → τcP i a ≡ nothing) → (∀ i a → τcQ i a ≡ nothing)
  → (∀ (at : AnyTypes E) (a : proj₁ at) → Blocked A B vP vQ at a)
  → IsStuck (P ⟦ A ∥ B ⟧ Q)
-- ret / sil steps: composite force is a `react` node, contradicting the constructor's
-- force equality (mirrors Semantics.Deadlock.deadlock-IsStuck).
αpar-IsStuck eqP eqQ _ _ _ (sRet eq) rewrite eqP | eqQ = case eq of λ ()
αpar-IsStuck eqP eqQ _ _ _ (sSil eq) rewrite eqP | eqQ = case eq of λ ()
-- visible step: the merged offer at (at , a) is `nothing`, contradicting branch-eq.
αpar-IsStuck {A = A} {B = B} {vP = vP} {vQ = vQ} eqP eqQ _ _ blocked
             (sVis {at = at} {a = a} feq branch-eq)
  rewrite eqP | eqQ with feq
... | refl with A .dec at a  | B .dec at a  | blocked at a
...   | yes _    | yes _    | lift bl with vP at a | vQ at a | bl
...     | nothing  | _        | inj₁ refl = case branch-eq of λ ()
...     | just _   | nothing  | inj₂ refl = case branch-eq of λ ()
αpar-IsStuck {A = A} {B = B} {vP = vP} eqP eqQ _ _ blocked (sVis {at = at} {a = a} feq branch-eq)
  | refl | yes _ | no _ | lift bl with vP at a | bl
...   | nothing | refl = case branch-eq of λ ()
αpar-IsStuck {A = A} {B = B} {vQ = vQ} eqP eqQ _ _ blocked (sVis {at = at} {a = a} feq branch-eq)
  | refl | no _ | yes _ | lift bl with vQ at a | bl
...   | nothing | refl = case branch-eq of λ ()
αpar-IsStuck eqP eqQ _ _ blocked (sVis {at = at} {a = a} feq branch-eq)
  | refl | no _ | no _ | _ = case branch-eq of λ ()
-- τ step: both operands are stable (τcP / τcQ everywhere `nothing`), and the
-- composite's τ-map (`αpar-pTau`) only forwards an operand τ — so every τ target
-- of the composite is `nothing`, refuting `τc i a ≡ just t′`.
αpar-IsStuck eqP eqQ stP stQ _
             (sTau {i = _ , base _}            feq branch-eq)
  rewrite eqP | eqQ with feq
... | refl = case branch-eq of λ ()
αpar-IsStuck eqP eqQ stP stQ _
             (sTau {i = _ , fin}               feq branch-eq)
  rewrite eqP | eqQ with feq
... | refl = case branch-eq of λ ()
αpar-IsStuck eqP eqQ stP stQ _
             (sTau {i = _ , pair (base _) _}   feq branch-eq)
  rewrite eqP | eqQ with feq
... | refl = case branch-eq of λ ()
αpar-IsStuck eqP eqQ stP stQ _
             (sTau {i = _ , pair (pair _ _) _} feq branch-eq)
  rewrite eqP | eqQ with feq
... | refl = case branch-eq of λ ()
αpar-IsStuck eqP eqQ stP stQ _
             (sTau {i = _ , pair fin i} {a = lift fzero , a} feq branch-eq)
  rewrite eqP | eqQ with feq
... | refl rewrite stP (_ , i) a = case branch-eq of λ ()
αpar-IsStuck eqP eqQ stP stQ _
             (sTau {i = _ , pair fin i} {a = lift (fsuc fzero) , a} feq branch-eq)
  rewrite eqP | eqQ with feq
... | refl rewrite stQ (_ , i) a = case branch-eq of λ ()
αpar-IsStuck eqP eqQ stP stQ _
             (sTau {i = _ , pair fin i} {a = lift (fsuc (fsuc _)) , a} feq branch-eq)
  rewrite eqP | eqQ with feq
... | refl = case branch-eq of λ ()

-------------------------------------------------------------------------------------
-- Elimination law: every trace of (P ⟦ A ∥ B ⟧ Q) decomposes into traces
-- of P and Q merged by alphabet-driven synchronisation (AlphaSync).
--
-- react port: the legacy ITree had SIX node kinds (ret/sil/vis/ndbr/mix), so the
-- elimination enumerated a 6×6 head-pair matrix with separate sNdbr / sMixSlide /
-- sMixVis transition rules.  Under the fused `react` node there are only THREE node
-- kinds (ret/sil/react) and FOUR transition rules (sRet/sSil/sVis/sTau).  Hence:
--   * the entire sNdbr block and all mix / sMixVis / sMixSlide blocks VANISH;
--   * internal choice / sliding now both fire `sTau` from a `react` head, so the
--     legacy `sNdbr` τ-cases are CONSOLIDATED into one `sTau` clause; and
--   * the τ-flush over a leading silent run uses BOTH `sSil` (a `sil`-head operand)
--     and `sTau` (a `react`-head operand whose τ-map forwards an operand τ).

private
  -- deadlock makes no LTS step, so its only big-step trace is the empty one.
  deadlock-trace-nil :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {s : List (Event√ {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} R)} {t′ : PTree E (ExtI I) R}
    → deadlock {E = E} {I = ExtI I} {R = R} ⟹⟨ s ⟩ t′
    → s ≡ [] × t′ ≡ deadlock
  deadlock-trace-nil ⟹-refl              = refl , refl
  deadlock-trace-nil (⟹-τ  (sSil eq) _)  = case eq of λ ()
  deadlock-trace-nil (⟹-τ  (sTau refl br) _) = case br of λ ()
  deadlock-trace-nil (⟹-ev (sRet eq) _)  = case eq of λ ()
  deadlock-trace-nil (⟹-ev (sVis refl br) _) = case br of λ ()

  -- τ-step inversion of the composite's fused τ-branch (`αpar-pTau`): a τ from the
  -- merged node is exactly P's τ (tag 0 → P′ ∥ Q) or Q's τ (tag 1 → P ∥ Q′).  This
  -- single inversion replaces the legacy `sNdbr`-on-pair + mix-slide case analysis.
  αpar-pTau-inv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A B : EventSet}
      {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
      {vP τcP vQ τcQ}
      {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) (R × S)))}
      {τc : (i  : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) (R × S)))}
      {i  : AnyTypes (ExtI I)} {a : proj₁ i} {M : PTree E (ExtI I) (R × S)}
    → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ react v τc
    → τc i a ≡ just M
    → (Σ[ j ∈ AnyTypes (ExtI I) ] Σ[ a′ ∈ proj₁ j ] Σ[ P′ ∈ PTree E (ExtI I) R ]
          (τcP j a′ ≡ just P′) × (M ≡ (P′ ⟦ A ∥ B ⟧ Q)))
    ⊎ (Σ[ j ∈ AnyTypes (ExtI I) ] Σ[ a′ ∈ proj₁ j ] Σ[ Q′ ∈ PTree E (ExtI I) S ]
          (τcQ j a′ ≡ just Q′) × (M ≡ (P ⟦ A ∥ B ⟧ Q′)))
  αpar-pTau-inv {i = _ , base _}            eqP eqQ feq br rewrite eqP | eqQ with feq
  ... | refl = case br of λ ()
  αpar-pTau-inv {i = _ , fin}               eqP eqQ feq br rewrite eqP | eqQ with feq
  ... | refl = case br of λ ()
  αpar-pTau-inv {i = _ , pair (base _) _}   eqP eqQ feq br rewrite eqP | eqQ with feq
  ... | refl = case br of λ ()
  αpar-pTau-inv {i = _ , pair (pair _ _) _} eqP eqQ feq br rewrite eqP | eqQ with feq
  ... | refl = case br of λ ()
  αpar-pTau-inv {τcP = τcP} {i = _ , pair fin j} {a = lift fzero , a′}
    eqP eqQ feq br rewrite eqP | eqQ with feq
  ... | refl with τcP (_ , j) a′ in pe
  ...   | just P′ = inj₁ ((_ , j) , a′ , P′ , pe , sym (just-injective br))
  ...   | nothing = case br of λ ()
  αpar-pTau-inv {τcQ = τcQ} {i = _ , pair fin j} {a = lift (fsuc fzero) , a′}
    eqP eqQ feq br rewrite eqP | eqQ with feq
  ... | refl with τcQ (_ , j) a′ in qe
  ...   | just Q′ = inj₂ ((_ , j) , a′ , Q′ , qe , sym (just-injective br))
  ...   | nothing = case br of λ ()
  αpar-pTau-inv {i = _ , pair fin j} {a = lift (fsuc (fsuc _)) , a′}
    eqP eqQ feq br rewrite eqP | eqQ with feq
  ... | refl = case br of λ ()

-- Visible-step inversion of the composite.  A single `sVis` out of (P ⟦A∥B⟧ Q) is
-- one of: a synchronisation (event in both A and B, both operands offer), a P-solo
-- (event in A only), a Q-solo (event in B only), or a joint √ (both operands at ret).
-- (The "event in neither alphabet" routing is refused — `αpar-pVis`/`-hVis*` map it
-- to `nothing` — so it never appears.)  This collapses the legacy `sVis`/`sMixVis`
-- disjunction: there is exactly ONE `react` head per side, fired by `sVis`.
data αVisR {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           (A B : EventSet)
           (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
     : PTree E (ExtI I) (R × S)
     → Event√ {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} (R × S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where
  vSync : ∀ {X} {e : E X} {a : X} {P′ Q′}
        → A .mem (X , e) a → B .mem (X , e) a
        → P ─[ ev (evl (evLabel X e a)) ]─► P′
        → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
        → αVisR A B P Q (P′ ⟦ A ∥ B ⟧ Q′) (evl (evLabel X e a))
  vSoloL : ∀ {X} {e : E X} {a : X} {P′}
         → A .mem (X , e) a → ¬ B .mem (X , e) a
         → P ─[ ev (evl (evLabel X e a)) ]─► P′
         → αVisR A B P Q (P′ ⟦ A ∥ B ⟧ Q) (evl (evLabel X e a))
  vSoloR : ∀ {X} {e : E X} {a : X} {Q′}
         → ¬ A .mem (X , e) a → B .mem (X , e) a
         → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
         → αVisR A B P Q (P ⟦ A ∥ B ⟧ Q′) (evl (evLabel X e a))
  v√ : ∀ {r : R} {s : S}
     → P .force ≡ ret r → Q .force ≡ ret s
     → αVisR A B P Q deadlock (√ (r , s))

private
  -- visible-offer inversion: drive the routing by (force P , force Q) and (da , db).
  -- Each non-refused, non-absurd quadrant rebuilds the αVisR routing witness.
  αpar-vis-inv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A B : EventSet}
      {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
      {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) (R × S)))}
      {τc : (i  : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) (R × S)))}
      {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI I) (R × S)}
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ react v τc → v at a ≡ just M
    → αVisR A B P Q M (evl (evLabel (proj₁ at) (proj₂ at) a))
  αpar-vis-inv {A = A} {B = B} {P = P} {Q = Q} {at = at} {a = a} feq br
    with PTree.force P in p-eq | PTree.force Q in q-eq
  -- ret | react : only the (no A , yes B) quadrant fires; Q acts solo.
  ... | ret r | react vQ τcQ with feq
  ...   | refl with A .dec at a | B .dec at a
  ...     | no ¬pA | yes pB with vQ at a in qe | br
  ...       | just Q′ | refl = vSoloR ¬pA pB (sVis q-eq qe)
  αpar-vis-inv feq br | ret r | react vQ τcQ | refl | no _ | yes _ | nothing | ()
  αpar-vis-inv feq br | ret r | react vQ τcQ | refl | yes _ | _    = case br of λ ()
  αpar-vis-inv feq br | ret r | react vQ τcQ | refl | no _  | no _ = case br of λ ()
  -- react | ret : only the (yes A , no B) quadrant fires; P acts solo.
  αpar-vis-inv {A = A} {B = B} {at = at} {a = a} feq br | react vP τcP | ret s with feq
  ...   | refl with A .dec at a | B .dec at a
  ...     | yes pA | no ¬pB with vP at a in pe | br
  ...       | just P′ | refl = vSoloL pA ¬pB (sVis p-eq pe)
  αpar-vis-inv feq br | react vP τcP | ret s | refl | yes _ | no _ | nothing | ()
  αpar-vis-inv feq br | react vP τcP | ret s | refl | no _  | _     = case br of λ ()
  αpar-vis-inv feq br | react vP τcP | ret s | refl | yes _ | yes _ = case br of λ ()
  -- ret | ret : the composite force is `ret (r , s)`, not react — absurd.
  αpar-vis-inv feq br | ret r | ret s = case feq of λ ()
  -- sil heads: composite force is `sil`, not react — absurd.
  αpar-vis-inv feq br | sil _ | _      = case feq of λ ()
  αpar-vis-inv feq br | ret _ | sil _  = case feq of λ ()
  αpar-vis-inv feq br | react _ _ | sil _ = case feq of λ ()
  -- react | react : the full 4-way routing.
  αpar-vis-inv {A = A} {B = B} {at = at} {a = a} feq br | react vP τcP | react vQ τcQ
    with feq
  ...   | refl with A .dec at a | B .dec at a
  ...     | yes pA | yes pB with vP at a in pe | vQ at a in qe | br
  ...       | just P′ | just Q′ | refl = vSync pA pB (sVis p-eq pe) (sVis q-eq qe)
  αpar-vis-inv feq br | react vP τcP | react vQ τcQ | refl | yes _ | yes _ | just _ | nothing | ()
  αpar-vis-inv feq br | react vP τcP | react vQ τcQ | refl | yes _ | yes _ | nothing | _ | ()
  αpar-vis-inv {at = at} {a = a} feq br | react vP τcP | react vQ τcQ | refl | yes pA | no ¬pB
    with vP at a in pe | br
  ...   | just P′ | refl = vSoloL pA ¬pB (sVis p-eq pe)
  αpar-vis-inv feq br | react vP τcP | react vQ τcQ | refl | yes _ | no _ | nothing | ()
  αpar-vis-inv {at = at} {a = a} feq br | react vP τcP | react vQ τcQ | refl | no ¬pA | yes pB
    with vQ at a in qe | br
  ...   | just Q′ | refl = vSoloR ¬pA pB (sVis q-eq qe)
  αpar-vis-inv feq br | react vP τcP | react vQ τcQ | refl | no _ | yes _ | nothing | ()
  αpar-vis-inv feq br | react vP τcP | react vQ τcQ | refl | no _ | no _ = case br of λ ()

  -- τ-step inversion: a τ out of (P ⟦A∥B⟧ Q) is P's τ (→ P′ ∥ Q) or Q's τ (→ P ∥ Q′).
  -- This consolidates the legacy sSil-distribution + sNdbr + sMixSlide cases into one:
  --   * a `sil`-headed operand fires `sSil` and the composite forces to `sil`;
  --   * a `react`-headed operand fires its τ-branch through the fused `αpar-pTau`.
  αpar-τ-inv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A B : EventSet}
      {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S} {M : PTree E (ExtI I) (R × S)}
    → (P ⟦ A ∥ B ⟧ Q) ─[ τ ]─► M
    → (Σ[ P′ ∈ PTree E (ExtI I) R ] (P ─[ τ ]─► P′) × (M ≡ (P′ ⟦ A ∥ B ⟧ Q)))
    ⊎ (Σ[ Q′ ∈ PTree E (ExtI I) S ] (Q ─[ τ ]─► Q′) × (M ≡ (P ⟦ A ∥ B ⟧ Q′)))
  -- sSil: the composite forces to `sil M`.  Decompose by which operand is sil-headed.
  αpar-τ-inv {P = P} {Q = Q} (sSil feq) with PTree.force P in p-eq | PTree.force Q in q-eq
  ... | sil P0 | _            = inj₁ (P0 , sSil p-eq , sym (sil-injective feq))
  ... | ret r  | sil Q0       = inj₂ (Q0 , sSil q-eq , sym (sil-injective feq))
  ... | react vP τcP | sil Q0 = inj₂ (Q0 , sSil q-eq , sym (sil-injective feq))
  ... | ret r  | ret s        = case feq of λ ()
  ... | ret r  | react _ _    = case feq of λ ()
  ... | react _ _ | ret s     = case feq of λ ()
  ... | react _ _ | react _ _ = case feq of λ ()
  -- sTau: the composite forces to `react` in three head-pairs.  Decode the fused τ-map:
  --   react|react → αpar-pTau (P's τ or Q's τ);  ret|react → αpar-hTauR (Q's τ);
  --   react|ret   → αpar-hTauL (P's τ).
  αpar-τ-inv {I = I} {R = R} {S = S} {A = A} {B = B} {P = P} {Q = Q}
             (sTau {i = i} {a = a} feq br)
    with PTree.force P in p-eq | PTree.force Q in q-eq
  -- react | react : decode αpar-pTau by the τ-index shape.
  ... | react vP τcP | react vQ τcQ =
        pp i a (case feq of λ { refl → br })
    where
      pp : ∀ j (a′ : proj₁ j) {M : PTree E (ExtI I) (R × S)}
         → αpar-pTau A B _,_ τcP τcQ P Q j a′ ≡ just M
         → (Σ[ P′ ∈ PTree E (ExtI I) R ] (P ─[ τ ]─► P′) × (M ≡ (P′ ⟦ A ∥ B ⟧ Q)))
         ⊎ (Σ[ Q′ ∈ PTree E (ExtI I) S ] (Q ─[ τ ]─► Q′) × (M ≡ (P ⟦ A ∥ B ⟧ Q′)))
      pp (_ , base _)            _  br = case br of λ ()
      pp (_ , fin)               _  br = case br of λ ()
      pp (_ , pair (base _) _)   _  br = case br of λ ()
      pp (_ , pair (pair _ _) _) _  br = case br of λ ()
      pp (_ , pair fin j) (lift fzero , a′)        br with τcP (_ , j) a′ in pe
      ... | just P′ = inj₁ (P′ , sTau p-eq pe , sym (just-injective br))
      ... | nothing = case br of λ ()
      pp (_ , pair fin j) (lift (fsuc fzero) , a′) br with τcQ (_ , j) a′ in qe
      ... | just Q′ = inj₂ (Q′ , sTau q-eq qe , sym (just-injective br))
      ... | nothing = case br of λ ()
      pp (_ , pair fin j) (lift (fsuc (fsuc _)) , a′) br = case br of λ ()
  -- ret | react : composite τ-map is αpar-hTauR, forwarding Q's τ at the same (i,a).
  ... | ret r | react vQ τcQ =
        qp (case feq of λ { refl → br })
    where
      qp : ∀ {M : PTree E (ExtI I) (R × S)}
         → αpar-hTauR A B _,_ r τcQ P Q i a ≡ just M
         → (Σ[ P′ ∈ PTree E (ExtI I) R ] (P ─[ τ ]─► P′) × (M ≡ (P′ ⟦ A ∥ B ⟧ Q)))
         ⊎ (Σ[ Q′ ∈ PTree E (ExtI I) S ] (Q ─[ τ ]─► Q′) × (M ≡ (P ⟦ A ∥ B ⟧ Q′)))
      qp br with τcQ i a in qe
      ... | just Q′ = inj₂ (Q′ , sTau q-eq qe , sym (just-injective br))
      ... | nothing = case br of λ ()
  -- react | ret : composite τ-map is αpar-hTauL, forwarding P's τ at the same (i,a).
  ... | react vP τcP | ret s =
        rp (case feq of λ { refl → br })
    where
      rp : ∀ {M : PTree E (ExtI I) (R × S)}
         → αpar-hTauL A B _,_ s τcP P Q i a ≡ just M
         → (Σ[ P′ ∈ PTree E (ExtI I) R ] (P ─[ τ ]─► P′) × (M ≡ (P′ ⟦ A ∥ B ⟧ Q)))
         ⊎ (Σ[ Q′ ∈ PTree E (ExtI I) S ] (Q ─[ τ ]─► Q′) × (M ≡ (P ⟦ A ∥ B ⟧ Q′)))
      rp br with τcP i a in pe
      ... | just P′ = inj₁ (P′ , sTau p-eq pe , sym (just-injective br))
      ... | nothing = case br of λ ()
  -- remaining head-pairs: composite force is `sil`/`ret`, not react — feq absurd.
  ... | sil _ | _          = case feq of λ ()
  ... | ret _ | sil _      = case feq of λ ()
  ... | ret _ | ret _      = case feq of λ ()
  ... | react _ _ | sil _  = case feq of λ ()

  -- the √-step inversion: composite force ≡ ret (r , s) forces both operands at ret.
  αpar-√-inv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A B : EventSet}
      {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S} {x : R × S}
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ ret x
    → αVisR A B P Q deadlock (√ x)
  αpar-√-inv {P = P} {Q = Q} feq with PTree.force P in p-eq | PTree.force Q in q-eq
  ... | ret r | ret s     = case feq of λ { refl → v√ p-eq q-eq }
  ... | ret _ | sil _     = case feq of λ ()
  ... | ret _ | react _ _ = case feq of λ ()
  ... | sil _ | _         = case feq of λ ()
  ... | react _ _ | ret _    = case feq of λ ()
  ... | react _ _ | sil _    = case feq of λ ()
  ... | react _ _ | react _ _ = case feq of λ ()

-- The elimination proper.  Structural recursion on the composite's big-step trace
-- derivation: each τ/visible head is inverted into the operand step(s) that produced
-- it (via αpar-τ-inv / αpar-vis-inv / αpar-√-inv), and the recursive call on the
-- (strictly smaller) tail supplies the merged AlphaSync + the operand sub-traces, to
-- which we prepend the just-inverted operand step.
AlphaParallel-trace-aux : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
  (A B : EventSet)
  {s : List (Event√ {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} (R × S))} {t′ : PTree E (ExtI I) (R × S)}
  → (P ⟦ A ∥ B ⟧ Q) ⟹⟨ s ⟩ t′
  → AlphaSyncSplit A B P Q s

-- 1. empty trace
AlphaParallel-trace-aux P Q A B ⟹-refl =
  in-progress sync-nil (_ , ⟹-refl) (_ , ⟹-refl)

-- 2. a τ-step: invert to P's τ (→ P′ ∥ Q) or Q's τ (→ P ∥ Q′), recurse, prepend.
AlphaParallel-trace-aux P Q A B (⟹-τ step rest)
  with αpar-τ-inv {P = P} {Q = Q} step
... | inj₁ (P′ , Pτ , refl) =
      case AlphaParallel-trace-aux P′ Q A B rest of λ where
        (in-progress merge (_ , trP′) trQ) →
          in-progress merge (_ , ⟹-τ Pτ trP′) trQ
        (done merge (_ , trP′) trQ) →
          done merge (_ , ⟹-τ Pτ trP′) trQ
... | inj₂ (Q′ , Qτ , refl) =
      case AlphaParallel-trace-aux P Q′ A B rest of λ where
        (in-progress merge trP (_ , trQ′)) →
          in-progress merge trP (_ , ⟹-τ Qτ trQ′)
        (done merge trP (_ , trQ′)) →
          done merge trP (_ , ⟹-τ Qτ trQ′)

-- 3. a √-step: composite at ret ⇒ both operands at ret.  After √ the residual is
-- `deadlock`, whose only trace is empty, so the whole trace ends here: `done`.
AlphaParallel-trace-aux P Q A B (⟹-ev (sRet feq) rest)
  with αpar-√-inv {P = P} {Q = Q} feq | deadlock-trace-nil rest
... | v√ pe qe | refl , refl =
      done sync-nil (_ , ⟹-ev (sRet pe) ⟹-refl) (_ , ⟹-ev (sRet qe) ⟹-refl)

-- 4. a visible event: invert the routing (sync / solo-L / solo-R), recurse, prepend.
AlphaParallel-trace-aux P Q A B (⟹-ev (sVis feq br) rest)
  with αpar-vis-inv {P = P} {Q = Q} feq br
... | vSync {e = e} {a = a} pA pB Pev Qev =
      case AlphaParallel-trace-aux _ _ A B rest of λ where
        (in-progress merge (_ , trP′) (_ , trQ′)) →
          in-progress (sync-both pA pB merge)
                      (_ , ⟹-ev Pev trP′) (_ , ⟹-ev Qev trQ′)
        (done merge (_ , trP′) (_ , trQ′)) →
          done (sync-both pA pB merge)
               (_ , ⟹-ev Pev trP′) (_ , ⟹-ev Qev trQ′)
... | vSoloL {e = e} {a = a} pA ¬pB Pev =
      case AlphaParallel-trace-aux _ Q A B rest of λ where
        (in-progress merge (_ , trP′) trQ) →
          in-progress (sync-l pA ¬pB merge) (_ , ⟹-ev Pev trP′) trQ
        (done merge (_ , trP′) trQ) →
          done (sync-l pA ¬pB merge) (_ , ⟹-ev Pev trP′) trQ
... | vSoloR {e = e} {a = a} ¬pA pB Qev =
      case AlphaParallel-trace-aux P _ A B rest of λ where
        (in-progress merge trP (_ , trQ′)) →
          in-progress (sync-r ¬pA pB merge) trP (_ , ⟹-ev Qev trQ′)
        (done merge trP (_ , trQ′)) →
          done (sync-r ¬pA pB merge) trP (_ , ⟹-ev Qev trQ′)

-- Public elimination (over the existential `traces`).
AlphaParallel-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
  (A B : EventSet)
  {s : List (Event√ {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} (R × S))}
  → traces (P ⟦ A ∥ B ⟧ Q) s
  → AlphaSyncSplit A B P Q s
AlphaParallel-trace P Q A B (_ , bs) = AlphaParallel-trace-aux P Q A B bs

-------------------------------------------------------------------------------------
-- INTRODUCTION direction: τ-flush + the restricted vis-driven introduction law.
--
-- react port note: STAGE 1's `αpar-ndbr-*` and STAGE 1b's `αpar-mix-slide-*` lemmas
-- are OBSOLETE — internal choice / sliding no longer use dedicated `ndbr`/`mix` nodes,
-- so there is no `sNdbr`/`sMixSlide` to build; an operand's internal τ now fires the
-- fused `react` τ-branch (`sTau`).  They are replaced by the single composite τ-step
-- lemma `αpar-τ`.  STAGE 3's `vis`-OR-`mix` disjunction collapses too: a head is one
-- `react` node fired by `sVis`, so the unprimed `αpar-sync-step`/`-soloL-step`/
-- `-soloR-step` (already provided by the operator module) ARE the step lemmas the
-- introduction needs — no `⊎`-of-mix arguments.

private
  -- A stable tree (react head, τc ≡ nothing) admits no τ-step.
  no-τ-from-stable :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t t′ : PTree E (ExtI I) R}
    → isStable t → t ─[ τ ]─► t′ → ⊥
  no-τ-from-stable {t = t} st (sSil eq)    with PTree.force t
  ... | react _ _ = case eq of λ ()
  no-τ-from-stable {t = t} st (sTau {i = i} {a = a} eq br) with PTree.force t
  ... | react _ τc′ =
        case trans (sym (st i a))
                   (subst (λ m → m i a ≡ just _) (sym (proj₂ (react-injective eq))) br)
             of λ ()

  -- A stable tree's only empty (τ-only) trace is the trivial one.
  stable-trace-nil :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t t′ : PTree E (ExtI I) R}
    → isStable t → t ⟹⟨ [] ⟩ t′ → t′ ≡ t
  stable-trace-nil st ⟹-refl       = refl
  stable-trace-nil st (⟹-τ s _)    = ⊥-elim (no-τ-from-stable st s)

  -- non-react heads are not stable.
  stable-not-sil :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t u : PTree E (ExtI I) R} → isStable t → t .force ≡ sil u → ⊥
  stable-not-sil {t = t} st eq with PTree.force t
  ... | react _ _ = case eq of λ ()
  stable-ret :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : PTree E (ExtI I) R} {r} → isStable t → t .force ≡ ret r → ⊥
  stable-ret {t = t} st eq with PTree.force t
  ... | react _ _ = case eq of λ ()

  -- a stable tree is react-headed; extract its offer function.
  isStable⇒react :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : PTree E (ExtI I) R}
    → isStable t
    → Σ[ v ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))) ]
      Σ[ τc ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))) ]
        t .force ≡ react v τc
  isStable⇒react {I = I} {R = R} {t = t} st = helper (t .force) refl st
    where
      helper : ∀ (n : NodeKind E (ExtI I) R) → t .force ≡ n → isStable t
             → Σ[ v ∈ _ ] Σ[ τc ∈ _ ] t .force ≡ react v τc
      helper (react v τc) eq _  = v , τc , eq
      helper (ret _) eq st = ⊥-elim (stable-ret {t = t} st eq)
      helper (sil _) eq st = ⊥-elim (stable-not-sil {t = t} st eq)

  -- a react-headed tree whose τc is everywhere nothing is stable.
  react⇒isStable :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : PTree E (ExtI I) R} {v τc}
    → t .force ≡ react v τc → (∀ i a → τc i a ≡ nothing) → isStable t
  react⇒isStable {t = t} eq tn with PTree.force t
  ... | react v τc rewrite proj₂ (react-injective eq) = tn

  -- concatenate a τ-only front with an arbitrary big-step.
  bigstep-++ :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {X Y Z : PTree E (ExtI I) R} {s : List (Event√ {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} R)}
    → X ⟹⟨ [] ⟩ Y → Y ⟹⟨ s ⟩ Z → X ⟹⟨ s ⟩ Z
  bigstep-++ ⟹-refl        bs = bs
  bigstep-++ (⟹-τ s front) bs = ⟹-τ s (bigstep-++ front bs)

-------------------------------------------------------------------------------------
-- STAGE 1: sil / τ composite single-step building blocks (introduction direction).

private
  αpar-fsil-L :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A B : EventSet}
      {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
    → P .force ≡ sil P′
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ sil (P′ ⟦ A ∥ B ⟧ Q)
  αpar-fsil-L eqP rewrite eqP = refl

  αpar-fsil-R :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A B : EventSet}
      {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
    → (∀ {t} → P .force ≢ sil t)
    → Q .force ≡ sil Q′
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ sil (P ⟦ A ∥ B ⟧ Q′)
  αpar-fsil-R {P = P} ¬sP eqQ with P .force
  ... | ret _     rewrite eqQ = refl
  ... | react _ _ rewrite eqQ = refl
  ... | sil _     = ⊥-elim (¬sP refl)

-- (1) P-sil advances unconditionally (operator clause 1).
αpar-sil-L :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A B : EventSet}
    {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
  → P .force ≡ sil P′
  → (P ⟦ A ∥ B ⟧ Q) ─[ τ ]─► (P′ ⟦ A ∥ B ⟧ Q)
αpar-sil-L eqP = sSil (αpar-fsil-L eqP)

-- (2) Q-sil advances only when P is not sil (operator clause 2).
αpar-sil-R :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A B : EventSet}
    {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
  → (∀ {t} → P .force ≢ sil t)
  → Q .force ≡ sil Q′
  → (P ⟦ A ∥ B ⟧ Q) ─[ τ ]─► (P ⟦ A ∥ B ⟧ Q′)
αpar-sil-R ¬sP eqQ = sSil (αpar-fsil-R ¬sP eqQ)

private
  -- composite is react when both operands are react-headed (force-reduction witness).
  αpar-freact :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A B : EventSet}
      {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S} {vP τcP vQ τcQ}
    → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ
    → Σ[ v ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) (R × S)))) ]
      Σ[ τc ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) (R × S)))) ]
        ((P ⟦ A ∥ B ⟧ Q) .force ≡ react v τc)
  αpar-freact eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  -- offer lemma: the composite's fused τ-map carries P's τ at tag 0.
  αpar-τ-offL-at :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A B : EventSet}
      {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
      {vP τcP vQ τcQ} {Ai} {ii : ExtI I Ai} {a : Ai}
      {v τc}
    → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ → τcP (Ai , ii) a ≡ just P′
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ react v τc
    → τc (_ , pair (fin {n = 2}) ii) (lift fzero , a) ≡ just (P′ ⟦ A ∥ B ⟧ Q)
  αpar-τ-offL-at eqP eqQ bP feq rewrite eqP | eqQ with feq
  ... | refl rewrite bP = refl

  -- offer lemma: the composite's fused τ-map carries Q's τ at tag 1.
  αpar-τ-offR-at :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A B : EventSet}
      {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
      {vP τcP vQ τcQ} {Ai} {ii : ExtI I Ai} {a : Ai}
      {v τc}
    → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ → τcQ (Ai , ii) a ≡ just Q′
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ react v τc
    → τc (_ , pair (fin {n = 2}) ii) (lift (fsuc fzero) , a) ≡ just (P ⟦ A ∥ B ⟧ Q′)
  αpar-τ-offR-at eqP eqQ bQ feq rewrite eqP | eqQ with feq
  ... | refl rewrite bQ = refl

-- ONE composite τ-step lemma over `sTau`, consolidating the legacy `αpar-ndbr-*` +
-- `αpar-mix-*`: an operand's internal τ (P's routed to composite tag 0 → P′ ∥ Q, Q's
-- routed to tag 1 → P ∥ Q′) fires the fused τ-branch of the merged react node.
αpar-τ-L :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A B : EventSet}
    {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
    {vP τcP vQ τcQ} {i : AnyTypes (ExtI I)} {a : proj₁ i}
  → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ → τcP i a ≡ just P′
  → (P ⟦ A ∥ B ⟧ Q) ─[ τ ]─► (P′ ⟦ A ∥ B ⟧ Q)
αpar-τ-L {i = Ai , ii} {a = a} eqP eqQ bP with αpar-freact eqP eqQ
... | v , τc , feq = sTau {i = _ , pair (fin {n = 2}) ii} {a = lift fzero , a} feq
                          (αpar-τ-offL-at eqP eqQ bP feq)

αpar-τ-R :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A B : EventSet}
    {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
    {vP τcP vQ τcQ} {i : AnyTypes (ExtI I)} {a : proj₁ i}
  → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ → τcQ i a ≡ just Q′
  → (P ⟦ A ∥ B ⟧ Q) ─[ τ ]─► (P ⟦ A ∥ B ⟧ Q′)
αpar-τ-R {i = Ai , ii} {a = a} eqP eqQ bQ with αpar-freact eqP eqQ
... | v , τc , feq = sTau {i = _ , pair (fin {n = 2}) ii} {a = lift (fsuc fzero) , a} feq
                          (αpar-τ-offR-at eqP eqQ bQ feq)

private
  -- shape refutations used to discharge the τ-flush priority hypotheses.
  ¬sil-of-ret :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : PTree E (ExtI I) R} {r} → t .force ≡ ret r → ∀ {u} → t .force ≢ sil u
  ¬sil-of-ret eq e = case trans (sym eq) e of λ ()
  ¬sil-of-react :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : PTree E (ExtI I) R} {v τc} → t .force ≡ react v τc → ∀ {u} → t .force ≢ sil u
  ¬sil-of-react eq e = case trans (sym eq) e of λ ()

-------------------------------------------------------------------------------------
-- STAGE 2: τ-flush — drive both operands through their leading τ's (respecting the
-- operator's sil-priority) to a pair of stable residuals.  react port: the legacy
-- ndbr / mix-slide clauses of the 9-way matrix collapse into the single react|react
-- case, where the leading operand τ is a `sTau` forwarded by the fused τ-branch.
-- Termination: each recursive call passes a strict sub-derivation (`restP`/`restQ`)
-- of the matched `⟹-τ`, driven by the step's own force-eq.

αpar-τ-flush : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A B : EventSet}
    {P P′ : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
  → P ⟹⟨ [] ⟩ P′ → Q ⟹⟨ [] ⟩ Q′ → isStable P′ → isStable Q′
  → (P ⟦ A ∥ B ⟧ Q) ⟹⟨ [] ⟩ (P′ ⟦ A ∥ B ⟧ Q′)
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ with P .force in p-eq | Q .force in q-eq
-- P sil-headed: consume P's leading τ (operator clause 1).
... | sil P0 | _ with bP
...   | ⟹-refl = ⊥-elim (stable-not-sil {t = P} stP p-eq)
...   | ⟹-τ (sSil e) restP =
        ⟹-τ (αpar-sil-L e) (αpar-τ-flush restP bQ stP stQ)
...   | ⟹-τ (sTau e _) _ = case trans (sym p-eq) e of λ ()
-- P ret-headed, Q sil-headed: consume Q's leading τ (operator clause 2).
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ret r | sil Q0 with bQ
...   | ⟹-refl = ⊥-elim (stable-not-sil {t = Q} stQ q-eq)
...   | ⟹-τ (sSil e) restQ =
        ⟹-τ (αpar-sil-R (¬sil-of-ret {t = P} p-eq) e) (αpar-τ-flush bP restQ stP stQ)
...   | ⟹-τ (sTau e _) _ = case trans (sym q-eq) e of λ ()
-- P react-headed, Q sil-headed: consume Q's leading τ.
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | react vP τcP | sil Q0 with bQ
...   | ⟹-refl = ⊥-elim (stable-not-sil {t = Q} stQ q-eq)
...   | ⟹-τ (sSil e) restQ =
        ⟹-τ (αpar-sil-R (¬sil-of-react {t = P} p-eq) e) (αpar-τ-flush bP restQ stP stQ)
...   | ⟹-τ (sTau e _) _ = case trans (sym q-eq) e of λ ()
-- both react-headed: a leading operand τ is a `sTau`; route P's (→ P′ ∥ Q) then Q's.
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | react vP τcP | react vQ τcQ with bP
...   | ⟹-τ (sTau eP bp) restP =
        ⟹-τ (αpar-τ-L eP q-eq bp) (αpar-τ-flush restP bQ stP stQ)
...   | ⟹-τ (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | ⟹-refl with bQ
...     | ⟹-τ (sTau eQ bq) restQ =
          ⟹-τ (αpar-τ-R p-eq eQ bq) (αpar-τ-flush ⟹-refl restQ stP stQ)
...     | ⟹-τ (sSil e) _ = case trans (sym q-eq) e of λ ()
...     | ⟹-refl = ⟹-refl
-- ret|ret, ret|react, react|ret with NO τ: a ret-headed operand is not stable, so its
-- empty trace must end at a non-stable residual — contradicting the stability premise.
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ret r | ret s with bP
...   | ⟹-refl = ⊥-elim (stable-ret {t = P} stP p-eq)
...   | ⟹-τ (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | ⟹-τ (sTau e _) _ = case trans (sym p-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ret r | react vQ τcQ with bP
...   | ⟹-refl = ⊥-elim (stable-ret {t = P} stP p-eq)
...   | ⟹-τ (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | ⟹-τ (sTau e _) _ = case trans (sym p-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | react vP τcP | ret s with bQ
...   | ⟹-refl = ⊥-elim (stable-ret {t = Q} stQ q-eq)
...   | ⟹-τ (sSil e) _ = case trans (sym q-eq) e of λ ()
...   | ⟹-τ (sTau e _) _ = case trans (sym q-eq) e of λ ()

-------------------------------------------------------------------------------------
-- STAGE 4: restricted introduction law (vis-headed visible events).
--
-- `VisDriven bs` asserts every VISIBLE step in `bs` is a `sVis` (fired from a `react`
-- head's vis-part); τ-steps (`sSil`/`sTau`) are unconstrained.  This is the exact
-- restriction under which the binary alphabetised parallel admits an introduction
-- law: synchronisation events come from genuine react `vis`-offers.

data VisDriven {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  : {X X′ : PTree E (ExtI I) R} {s : List (Event√ {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} R)}
  → X ⟹⟨ s ⟩ X′ → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  vd-nil  : ∀ {X} → VisDriven (⟹-refl {p = X})
  vd-tau  : ∀ {X X′ X″ s} {τstep : X ─[ τ ]─► X′} {rest : X′ ⟹⟨ s ⟩ X″}
          → VisDriven rest → VisDriven (⟹-τ τstep rest)
  vd-vis  : ∀ {X X′ X″ at a v τc s} {rest : X′ ⟹⟨ s ⟩ X″}
          → (fe : X .force ≡ react v τc) → (je : v at a ≡ just X′)
          → VisDriven rest
          → VisDriven (⟹-ev
              (sVis {p = X} {v = v} {τc = τc} {at = at} {a = a} {t′ = X′} fe je) rest)

-- Front split landing at a react head: a vis-driven big-step decomposes into leading
-- τ's to a react-headed X₁ followed by EITHER (empty trace) the endpoint reached, OR
-- (cons trace) the visible offer at X₁ and the vis-driven tail.  The SUM exposes the
-- head shape so the caller need not re-case the (existential) tail's VisDriven.
LeadVis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            (X X′ : PTree E (ExtI I) R)
            (s : List (Event√ {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} R))
        → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
LeadVis {ℓi = ℓi} {I = I} {R = R} X X′ s =
  Σ[ X₁ ∈ PTree E (ExtI I) R ] Σ[ vX₁ ∈ _ ] Σ[ τcX₁ ∈ _ ]
    (X ⟹⟨ [] ⟩ X₁ × X₁ .force ≡ react vX₁ τcX₁
     × Σ[ bs₁ ∈ (X₁ ⟹⟨ s ⟩ X′) ] VisDriven bs₁          -- residual from X₁ (for stationary side)
     × ((s ≡ [] × X₁ ≡ X′)
        ⊎ (Σ[ e ∈ Event {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} ] Σ[ rest ∈ _ ] Σ[ X₂ ∈ _ ]
               (s ≡ evl e ∷ rest
                × vX₁ (Event.A e , Event.e e) (Event.a e) ≡ just X₂
                × Σ[ bs₂ ∈ (X₂ ⟹⟨ rest ⟩ X′) ] VisDriven bs₂))))

lead-split-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {X X′ : PTree E (ExtI I) R} {s : List (Event√ {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} R)}
    (bs : X ⟹⟨ s ⟩ X′)
  → VisDriven bs → isStable X′ → LeadVis X X′ s
lead-split-vis {X = X} {X′ = X′} ⟹-refl vd-nil stX′ with isStable⇒react {t = X′} stX′
... | v , τc , eq = X′ , v , τc , ⟹-refl , eq , ⟹-refl , vd-nil , inj₁ (refl , refl)
lead-split-vis (⟹-τ τstep rest) (vd-tau vd) stX′ with lead-split-vis rest vd stX′
... | X₁ , vX₁ , τcX₁ , flush , eq , bs₁ , vd₁ , sum =
      X₁ , vX₁ , τcX₁ , ⟹-τ τstep flush , eq , bs₁ , vd₁ , sum
lead-split-vis {X = X} (⟹-ev (sVis {at = at} {a = a} fe je) rest) (vd-vis _ _ vd) _ =
  X , _ , _ , ⟹-refl , fe ,
  ⟹-ev (sVis fe je) rest , vd-vis fe je vd ,
  inj₂ (evLabel (proj₁ at) (proj₂ at) a , _ , _ , refl , je , rest , vd)

-- A τ-only run congruence: replay GIVEN leading-τ runs of P and Q (ending at
-- react-headed residuals, not necessarily stable) as a τ-only run of the composite.
-- Unlike `αpar-τ-flush` this does NOT need stability of the endpoints — react-headed
-- suffices to rule out the `sil`-priority forced-step at the endpoints — which is what
-- the introduction needs at the pre-visible-event heads `P₁`/`Q₁`.
αpar-flush-react : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A B : EventSet}
    {P P′ : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S} {vP τcP vQ τcQ}
  → P ⟹⟨ [] ⟩ P′ → Q ⟹⟨ [] ⟩ Q′
  → P′ .force ≡ react vP τcP → Q′ .force ≡ react vQ τcQ
  → (P ⟦ A ∥ B ⟧ Q) ⟹⟨ [] ⟩ (P′ ⟦ A ∥ B ⟧ Q′)
αpar-flush-react {P = P} {Q = Q} bP bQ rP rQ with P .force in p-eq | Q .force in q-eq
... | sil P0 | _ with bP
...   | ⟹-refl = ⊥-elim (case trans (sym rP) p-eq of λ ())
...   | ⟹-τ (sSil e) restP = ⟹-τ (αpar-sil-L e) (αpar-flush-react restP bQ rP rQ)
...   | ⟹-τ (sTau e _) _ = case trans (sym p-eq) e of λ ()
αpar-flush-react {P = P} {Q = Q} bP bQ rP rQ | ret r | sil Q0 with bQ
...   | ⟹-refl = ⊥-elim (case trans (sym rQ) q-eq of λ ())
...   | ⟹-τ (sSil e) restQ =
        ⟹-τ (αpar-sil-R (¬sil-of-ret {t = P} p-eq) e) (αpar-flush-react bP restQ rP rQ)
...   | ⟹-τ (sTau e _) _ = case trans (sym q-eq) e of λ ()
αpar-flush-react {P = P} {Q = Q} bP bQ rP rQ | react vP τcP | sil Q0 with bQ
...   | ⟹-refl = ⊥-elim (case trans (sym rQ) q-eq of λ ())
...   | ⟹-τ (sSil e) restQ =
        ⟹-τ (αpar-sil-R (¬sil-of-react {t = P} p-eq) e) (αpar-flush-react bP restQ rP rQ)
...   | ⟹-τ (sTau e _) _ = case trans (sym q-eq) e of λ ()
αpar-flush-react {P = P} {Q = Q} bP bQ rP rQ | react vP τcP | react vQ τcQ with bP
...   | ⟹-τ (sTau eP bp) restP =
        ⟹-τ (αpar-τ-L eP q-eq bp) (αpar-flush-react restP bQ rP rQ)
...   | ⟹-τ (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | ⟹-refl with bQ
...     | ⟹-τ (sTau eQ bq) restQ =
          ⟹-τ (αpar-τ-R p-eq eQ bq) (αpar-flush-react ⟹-refl restQ rP rQ)
...     | ⟹-τ (sSil e) _ = case trans (sym q-eq) e of λ ()
...     | ⟹-refl = ⟹-refl
-- ret base cases: a react-headed endpoint reached by an empty run from a ret head is
-- impossible (ret heads have no τ, so P′ = P would be ret, contradicting `react`).
αpar-flush-react {P = P} {Q = Q} bP bQ rP rQ | ret r | ret s with bP
...   | ⟹-refl = ⊥-elim (case trans (sym rP) p-eq of λ ())
...   | ⟹-τ (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | ⟹-τ (sTau e _) _ = case trans (sym p-eq) e of λ ()
αpar-flush-react {P = P} {Q = Q} bP bQ rP rQ | ret r | react vQ τcQ with bP
...   | ⟹-refl = ⊥-elim (case trans (sym rP) p-eq of λ ())
...   | ⟹-τ (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | ⟹-τ (sTau e _) _ = case trans (sym p-eq) e of λ ()
αpar-flush-react {P = P} {Q = Q} bP bQ rP rQ | react vP τcP | ret s with bQ
...   | ⟹-refl = ⊥-elim (case trans (sym rQ) q-eq of λ ())
...   | ⟹-τ (sSil e) _ = case trans (sym q-eq) e of λ ()
...   | ⟹-τ (sTau e _) _ = case trans (sym q-eq) e of λ ()

-------------------------------------------------------------------------------------
-- The restricted introduction law.  Given a synchronisation split `AlphaSync A B sP
-- sQ s` and vis-driven component big-steps for P and Q ending at stable (react)
-- residuals, the binary alphabetised parallel performs the merged trace `map evl s`,
-- ending at the composite of the residuals.

αpar-trace-intro : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A B : EventSet}
    {P P′ : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
    {sP sQ s : List (Event {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I})}
  → AlphaSync {I = I} A B sP sQ s
  → (bP : P ⟹⟨ map evl sP ⟩ P′) → VisDriven bP
  → (bQ : Q ⟹⟨ map evl sQ ⟩ Q′) → VisDriven bQ
  → isStable P′ → isStable Q′
  → (P ⟦ A ∥ B ⟧ Q) ⟹⟨ map evl s ⟩ (P′ ⟦ A ∥ B ⟧ Q′)

-- empty: both operands τ-flush to their stable endpoints.
αpar-trace-intro sync-nil bP _ bQ _ stP stQ = αpar-τ-flush bP bQ stP stQ

-- synchronisation: P and Q both fire `e`.  Each operand flushes its leading τ's to a
-- react head, fires `e` via sVis (operator `αpar-sync-step`), then tails recurse.
αpar-trace-intro (sync-both {e = e} pA pB rest)
                 bP vdP bQ vdQ stP stQ
  with lead-split-vis bP vdP stP | lead-split-vis bQ vdQ stQ
... | P₁ , vP₁ , τcP₁ , flushP , eqP₁ , _ , _ , inj₂ (_ , _ , _ , refl , jeP , bP₂ , vdP₂)
    | Q₁ , vQ₁ , τcQ₁ , flushQ , eqQ₁ , _ , _ , inj₂ (_ , _ , _ , refl , jeQ , bQ₂ , vdQ₂) =
      bigstep-++ (αpar-flush-react flushP flushQ eqP₁ eqQ₁)
        (⟹-ev (αpar-sync-step pA pB eqP₁ jeP eqQ₁ jeQ)
          (αpar-trace-intro rest bP₂ vdP₂ bQ₂ vdQ₂ stP stQ))

-- solo-L: P fires `e` (in A only), Q stationary (Q's own trace resumed from Q₁).
αpar-trace-intro (sync-l {e = e} pA ¬pB rest)
                 bP vdP bQ vdQ stP stQ
  with lead-split-vis bP vdP stP | lead-split-vis bQ vdQ stQ
... | P₁ , vP₁ , τcP₁ , flushP , eqP₁ , _ , _ , inj₂ (_ , _ , _ , refl , jeP , bP₂ , vdP₂)
    | Q₁ , vQ₁ , τcQ₁ , flushQ , eqQ₁ , bQ₁ , vdQ₁ , _ =
      bigstep-++ (αpar-flush-react flushP flushQ eqP₁ eqQ₁)
        (⟹-ev (αpar-soloL-step pA ¬pB eqP₁ jeP eqQ₁)
          (αpar-trace-intro rest bP₂ vdP₂ bQ₁ vdQ₁ stP stQ))

-- solo-R: Q fires `e` (in B only), P stationary (P's own trace resumed from P₁).
αpar-trace-intro (sync-r {e = e} ¬pA pB rest)
                 bP vdP bQ vdQ stP stQ
  with lead-split-vis bP vdP stP | lead-split-vis bQ vdQ stQ
... | P₁ , vP₁ , τcP₁ , flushP , eqP₁ , bP₁ , vdP₁ , _
    | Q₁ , vQ₁ , τcQ₁ , flushQ , eqQ₁ , _ , _ , inj₂ (_ , _ , _ , refl , jeQ , bQ₂ , vdQ₂) =
      bigstep-++ (αpar-flush-react flushP flushQ eqP₁ eqQ₁)
        (⟹-ev (αpar-soloR-step ¬pA pB eqP₁ eqQ₁ jeQ)
          (αpar-trace-intro rest bP₁ vdP₁ bQ₂ vdQ₂ stP stQ))

private
  module Sanity where
    open CSPOps using (Stop)

    -- `Stop`'s force is `react ∅v ∅t`, both maps everywhere `nothing`.
    stop∥stop-stuck :
      ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {A B : EventSet}
      → IsStuck (Stop {R = R} ⟦ A ∥ B ⟧ Stop {R = S})
    stop∥stop-stuck {A = A} {B = B} =
      αpar-IsStuck refl refl (λ _ _ → refl) (λ _ _ → refl) blocked
      where
        blocked : ∀ at a → Blocked A B _ _ at a
        blocked at a with A .dec at a | B .dec at a
        ... | yes _ | yes _ = lift (inj₁ refl)
        ... | yes _ | no  _ = lift refl
        ... | no  _ | yes _ = lift refl
        ... | no  _ | no  _ = tt

    stop∥stop-hasDeadlock :
      ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {A B : EventSet}
      → HasDeadlock (Stop {R = R} ⟦ A ∥ B ⟧ Stop {R = S})
    stop∥stop-hasDeadlock = [] , _ , ⟹-refl , stop∥stop-stuck
