{-
  This module defines the traces semantics for CSP.
-}

{-# OPTIONS --guardedness #-}

open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Unary using (∅)
open import Function using (case_of_)
open import Relation.Nullary using (¬_;Dec; yes; no; contradiction)
-- open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _++_; _∷_; []; [_]; length; reverse; map; foldr; downFrom)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional as Relation
open Relation using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym; trans; refl; inspect; cong)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import Class.DecEq using (DecEq; _≟_)

open import Interaction_Trees
open import CSP.Basic_Processes
open import ITree_Relations.LTS

module CSP.Traces {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where
open ITree
open Traces

-----------------------------------------------------------------
-- Stop makes no τ step
Stop-no-τ :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t′ : ITree E I R}
  → Stop ─[ τ ]─► t′
  → ⊥
Stop-no-τ tr = τ-from-force-vis-impossible refl tr
  
-- Stop makes no ev step
-- If nothing ≡ just t', then we can produce ⊥
Stop-no-evl :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t′ : ITree E I R}
    {A : Set ℓ} {e : E A} {a : A}        
  → Stop ─[ ev (evl (evLabel A e a)) ]─► t′
  → ⊥
Stop-no-evl {t′ = t′} {A = A} {e = e} {a = a} tr with ev-ndbr tr
... | f , (force≡vis , f-eq) =
  nothing≢just
    (subst (λ g → g (A , e) a ≡ just _)
           (vis-injective (sym force≡vis))   -- f ≡ λ _ _ → nothing
           f-eq)                        -- f (A , e) a ≡ just t′
  where
    nothing≢just : nothing ≡ just _ → ⊥
    nothing≢just ()

-- Stop makes no tick step
Stop-no-√ :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t′ : ITree E I R} {x : R}
  → Stop ─[ ev (√ x) ]─► t′
  → ⊥
Stop-no-√ (sRet force≡ret) = case force≡ret of λ ()

-- Stop makes no ev step
-- If nothing ≡ just t', then we can produce ⊥
Stop-no-ev :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t′ : ITree E I R}
    {e : Event√ E R}
  → Stop ─[ ev e ]─► t′
  → ⊥
Stop-no-ev {e = evl (evLabel _ _ _)} step = Stop-no-evl step
Stop-no-ev {e = √ x}                  step = Stop-no-√  step

-- Stop makes no visible transition
Stop-no-steps : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {s : List (Event√ E R)} {t′ : ITree E I R}
  → Stop ═⟨ s ⟩═► t′
  → s ≡ []
Stop-no-steps bNil          = refl
Stop-no-steps (bTau τ-step _)  = ⊥-elim (Stop-no-τ τ-step)
Stop-no-steps (bStep ev-step _) = ⊥-elim (Stop-no-ev ev-step)

-- The traces of Stop is empty
Stop-traces-empty : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {s : List (Event√ E R)}
  → traces {I = I} Stop s
  → s ≡ []
Stop-traces-empty (_ , der) = Stop-no-steps der

{-
Stop-traces-empty : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
    {s : List (Event√ E (⊤ {ℓr}))}
  → traces {I = I} Stop s
  → s ≡ []
Stop-traces-empty {ℓr = ℓr} tr = Stop-traces-empty {R = (⊤ {ℓr})} tr
-}

-- Any ITree refines Stop
⊑ᵀ-Stop : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    (t : ITree E I R)
  → t ⊑ᵀ Stop
⊑ᵀ-Stop t (_ , der) with Stop-no-steps der
... | refl = t , bNil

-----------------------------------------------------------------------------------------
-- Terminate and Skip
Ret-trace : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {x : R} {s : List (Event√ E R)}
  → traces {I = I} (Ret x) s
  → s ≡ [] ⊎ s ≡ (√ x ∷ [])
Ret-trace (_ , bNil) = inj₁ refl
Ret-trace (_ , bTau (sSil ()) _)
Ret-trace (_ , bTau (sNdbr () _) _)
Ret-trace (_ , bStep (sRet refl) bNil) = inj₂ refl
Ret-trace (_ , bStep (sRet refl) (bTau (sSil ()) _))
Ret-trace (_ , bStep (sRet refl) (bTau (sNdbr () _) _))
Ret-trace (_ , bStep (sRet refl) (bStep (sRet ()) _))
Ret-trace (_ , bStep (sRet refl) (bStep (sVis refl ()) _))

Skip-trace : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
  {s : List (Event√ E (⊤ {ℓr}))}
  → traces {I = I} Skip s
  → s ≡ [] ⊎ s ≡ (√ tt ∷ [])
Skip-trace tr = Ret-trace tr

-----------------------------------------------------------------------------------------
-- Guard

guard-trace : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
    {b : Bool} {s : List (Event√ E (⊤ {ℓr}))}
  → traces {I = I} (guard b) s
  → (b ≡ true  × (s ≡ [] ⊎ s ≡ (√ tt ∷ [])))
  ⊎ (b ≡ false × s ≡ [])

guard-trace {b = true}  tr = inj₁ (refl , Skip-trace tr)
guard-trace {b = false} tr = inj₂ (refl , Stop-traces-empty tr)

-----------------------------------------------------------------------------------------
-- Run

-- √ x is not in the trace of Run
Run-no-Ret : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  {s : List (Event√ E R)} {x : R}
  → traces {I = I} Run s
  → √ x ∉ s
-- Case 1: The trace is empty. 
-- We don't care what the resulting ITree is, so we use _ for the first part of the pair.
Run-no-Ret (_ , bNil) ()

-- The Tau case is impossible because Run is a 'vis' node
Run-no-Ret (_ , bTau (sSil ()) _) 
Run-no-Ret (_ , bTau (sNdbr () _) _)

-- The step case.
-- 'bStep' proves that Run transitioned to a new state (which is also Run) via a visible event.
Run-no-Ret (._ , bStep (sVis refl refl) step-proof) (here ()) 
Run-no-Ret (._ , bStep (sVis refl refl) step-proof) (there mem) = 
  Run-no-Ret (_ , step-proof) mem 

-- Every event in the traces of Run is a visible event.
Run-trace : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  {s : List (Event√ E R)}
  → traces {I = I} Run s
  → ∀ {e} → e ∈ s → ∃ λ (lbl : Event E) → e ≡ evl lbl
Run-trace (_ , bNil) ()

-- By matching on (sVis refl refl), you prove to Agda that:
-- 1. The event is exactly what Run defines.
-- 2. The NEXT state (t') is exactly Run.
Run-trace (._ , bStep (sVis refl refl) big-step) (here refl) = 
  _ , refl

-- Now Agda knows 'big-step' has type 'Run ═⟨ tail ⟩═► t''
Run-trace (._ , bStep (sVis refl refl) big-step) (there mem) = 
  Run-trace (_ , big-step) mem

-- Handle the impossible Tau case similarly if needed
Run-trace (_ , bTau (sSil ()) _) _

-----------------------------------------------------------------------------------------
-- Run on a subset of events

Run′-trace : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (es : AnyTypes E → Set) (dec : (at : AnyTypes E) → Dec (es at))
  {s : List (Event√ E R)}
  → traces {I = I} (Run′ es dec) s
  → ∀ {e} → e ∈ s → ∃ λ (lbl : Event E) → (e ≡ evl lbl) × (es (Event.A lbl , Event.e lbl))

Run′-trace es dec (_ , bNil) ()
Run′-trace es dec (_ , bTau (sSil ()) _) _
Run′-trace es dec (_ , bStep (sRet ()) _) _
Run′-trace es dec (_ , bStep {el = evl (evLabel A action response)}
                              -- We use refl for eq-force to unify f with the case-logic
                              (sVis {at = at} {a = a} refl eq-just)
                              big-step) mem
  with dec at | mem
-- Branch: No ¬p. 
-- Since we matched eq-force with refl, eq-just now has type:
-- (case dec at of ...) ≡ just t'. 
-- In this branch, that simplifies to: nothing ≡ just t'.
... | no ¬p      | _         = ⊥-elim (case eq-just of λ ())

-- Branch: Yes p.
-- Here, (case dec at of ...) simplifies to: just (Run' es dec) ≡ just t'.
-- Thus t' is unified with Run' es dec.
... | yes p      | here refl = evLabel A action response , refl , p
... | yes p      | there m   = Run′-trace es dec (_ , subst (λ t → t ═⟨ _ ⟩═► _) t'-eq big-step) m
    where 
      -- Extract t' ≡ Run' es dec from (just (Run' es dec) ≡ just t')
      t'-eq : _ ≡ Run′ es dec
      t'-eq with dec at
      ... | yes _ = sym (just-injective eq-just)
      ... | no ¬p = contradiction p ¬p

-----------------------------------------------------------------------------------------
-- For CSP Operators
-----------------------------------------------------------------------------------------

import CSP.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

-----------------------------------------------------------------------------------------
-- Prefix
-- traces [a → P] = {⟨⟩} ∪ {t : traces [P] • ⟨a⟩ ̂  t}

Prefix-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (ch : E A) (P : A → ITree E (ExtI I) R)
  {s : List (Event√ E R)}
  → traces (Prefix ch P) s
  → s ≡ [] ⊎ (∃ λ (a : A) → ∃ λ (s' : List (Event√ E R)) → 
      (s ≡ evl (evLabel A ch a) ∷ s') × traces (P a) s')

Prefix-trace ch P (_ , bNil) = inj₁ refl
Prefix-trace {A = A} ch P (._ , bStep (sVis {at = at} {a = a} refl eq-j) big-step) 
    with E-≟ (A , ch) at
-- Branch: The event doesn't match the prefix.
-- Prefix definition says result is 'nothing', but bStep says 'just t''.
... | no  _ = ⊥-elim (case eq-j of λ ())

-- Branch: The event matches!
... | yes refl = 
    -- Now (A, ch) ≡ (A', ch'). Agda unifies A and ch'.
    -- eq-j now implies: just (P a) ≡ just t', so t' ≡ P a.
    let t'-is-P : _ ≡ P a
        t'-is-P = just-injective (sym eq-j)
    in inj₂ (a , _ , refl , (_ , subst (λ t → t ═⟨ _ ⟩═► _) t'-is-P big-step))

Prefix-trace ch P (_ , bTau (sSil ()) _)
Prefix-trace ch P (_ , bStep (sRet ()) _)

-- For simplified prefix, the response is ignored but it is stilled recorded in traces
Prefix₀-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (ch : E A) (Px : ITree E (ExtI I) R)
  {s : List (Event√ E R)}
  → traces (Prefix₀ ch Px) s
  → s ≡ [] ⊎ (∃ λ (a : A) → ∃ λ (s' : List (Event√ E R)) → 
      (s ≡ evl (evLabel A ch a) ∷ s') × traces Px s')
Prefix₀-trace ch Px = Prefix-trace ch (λ _ → Px)

-----------------------------------------------------------------------------------------
-- trigger

trigger-trace : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
  (e : E A) {s : List (Event√ E A)}
  → traces (trigger {ℓi = ℓi} {I = I} e) s
  → s ≡ [] 
  ⊎ (∃ λ (a : A) → s ≡ evl (evLabel A e a) ∷ [])
  ⊎ (∃ λ (a : A) → s ≡ evl (evLabel A e a) ∷ √ a ∷ [])

trigger-trace e (_ , bNil) = inj₁ refl
trigger-trace e (._ , bStep {el = el} (sVis {at = at} {a = a} refl eq-j) big-step)
  with E-≟ (_ , e) at
... | no _ = ⊥-elim (case eq-j of λ ())
... | yes refl = 
    let 
      -- The next state is Ret a
      t'-is-Ret : _ ≡ Ret a
      t'-is-Ret = just-injective (sym eq-j)
      
      -- Get the trace of the remainder from our Ret-trace lemma
      ret-tr : traces (Ret a) _
      ret-tr = _ , subst (λ t → t ═⟨ _ ⟩═► _) t'-is-Ret big-step
    in 
    case Ret-trace ret-tr of λ where
      (inj₁ s'≡[]) → 
        inj₂ (inj₁ (a , cong (λ x → evl (evLabel _ e a) ∷ x) s'≡[]))
      (inj₂ s'≡√)  → 
        inj₂ (inj₂ (a , cong (λ x → evl (evLabel _ e a) ∷ x) s'≡√))

trigger-trace e (_ , bTau (sSil ()) _)

-----------------------------------------------------------------------------------------
-- Internal choice ⊓
-- traces [P ⊓ Q] = traces [P] ∪ traces [Q]

InternalChoice-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (P Q : ITree E (ExtI I) R) {s : List (Event√ E R)}
  → traces {I = ExtI I} {R = R} (_⊓_ {I = I} {R = R} P Q) s
  → traces P s ⊎ traces Q s

InternalChoice-trace P Q (_ , bNil) = inj₁ (_ , bNil)

-- Internal choice cannot take visible or return steps directly
InternalChoice-trace P Q (_ , bStep (sVis () _) _)
InternalChoice-trace P Q (_ , bStep (sRet ()) _)

InternalChoice-trace P Q (._ , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) 
  with i | a | eq-f
-- Case: Branch fzero (P)
-- By matching eq-f as refl, Agda now knows f is br2. 
-- br2 (_ , fin) (lift fzero) simplifies definitionally to (just P).
... | (_ , fin) | (lift fzero) | refl = 
    -- Now eq-j has type: just P ≡ just t'
    let t'-is-P = just-injective eq-j
    in inj₁ (_ , subst (λ t → t ═⟨ _ ⟩═► _) (sym t'-is-P) big-step)

-- Case: Branch fsuc fzero (Q)
... | (_ , fin) | (lift (fsuc fzero)) | refl = 
    -- Now eq-j has type: just Q ≡ just t'
    let t'-is-Q = just-injective eq-j
    in inj₂ (_ , subst (λ t → t ═⟨ _ ⟩═► _) (sym t'-is-Q) big-step)
 
-----------------------------------------------------------------------------------------
-- External choice □
-- traces [P □ Q] = traces [P] ∪ traces [Q]

{-# NON_TERMINATING #-}
ExternalChoice-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} 
  {s : List (Event√ E R)}
  ⦃ dec : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R) 
  → traces {I = ExtI I} {R = R} (_□_ {I = I} {R = R} P Q) s
  → traces P s ⊎ traces Q s

-- 1. Empty trace
ExternalChoice-trace {ℓr = ℓr} {I = I} {R = R} {s = s} P Q (._ , bNil) = inj₁ (_ , bNil)

-- 2. Tau steps (Choice not yet resolved)
ExternalChoice-trace {ℓr = ℓr} {I = I} {R = R} {s = s} P Q (._ , bTau (sSil {t = next} eq-f) big-step) 
  with P .force in p-eq | Q .force in q-eq | eq-f

-- Case: P took a silent step. 
-- By matching eq-f as refl (or using it in a 'with'), Agda knows next is (P' □ Q).
... | sil P' | _ | refl = 
    case ExternalChoice-trace P' Q (_ , big-step) of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , bTau (sSil p-eq) trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , trQ)

-- Case: Q took a silent step
... | ret _ | sil Q' | refl = 
    case ExternalChoice-trace P Q' (_ , big-step) of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , bTau (sSil q-eq) trQ)

-- Case: Q took a silent step
... | vis _ | sil Q' | refl = 
    case ExternalChoice-trace P Q' (_ , big-step) of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , bTau (sSil q-eq) trQ)

-- Case: Q took a silent step
... | ndbr _ _ _ _ | sil Q' | refl = 
    case ExternalChoice-trace P Q' (_ , big-step) of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , bTau (sSil q-eq) trQ)
      
-- These cases are impossible because (ret □ ret) or (vis □ vis) 
-- are not silent nodes.
-- eq-f : (force ((E-≟ CSP.Operators.□ P) Q) ≡ sil t

--------------------------------------------------------------------------------------
-- For the "ret r1" and "ret r2" case, it is a bit complicated because the definition
-- of □ relies on a Dec to reduce it to "ret r1" if r1 = r2, or Stop otherwise.

ExternalChoice-trace {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | ret r1 | ret r2 | _ with r1 ≟ r2
-- match with r1 ≟ r2: yes
...                     | yes refl rewrite p-eq | q-eq with r1 ≟ r1
-- match with r1 ≟ r1: yes
...                                                     | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | ret r1 | ret r2 | _ | _
-- match with r1 ≟ r1: no
                                                        | no neq with eq-f
...                                                               | ()

ExternalChoice-trace {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | ret r1 | ret r2 | _
-- match with r1 ≟ r2: no    
                       | no neq rewrite p-eq | q-eq with r1 ≟ r2
-- match the 2nd with r1 ≟ r2 : yes
...                                                    | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | ret r1 | ret r2 | _ | _
-- match the 2nd with r1 ≟ r2 : no  
                                                       | no neq with eq-f
...                                                                 | ()

--------------------------------------------------------------------------------------

ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | ret _  | vis _  | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | vis _  | ret _  | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | vis _  | vis _  | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | vis _  | ndbr _ _ _ _ | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | ndbr _ _ _ _ | vis _  | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | ret _  | ndbr _ _ _ _ | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sSil {t = next} eq-f) big-step)
  | ndbr _ _ _ _ | ret _  | ()

-- 3. Visible steps (Choice resolved)
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step) 
  with P .force in p-eq | Q .force in q-eq | eq-f
... | vis fP | vis fQ | refl
    with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- just P' / nothing → mergeVis = just P', eq-j : just P' ≡ just t'
-- refl unifies t' = P', big-step : P' ═⟨ s ⟩═► _ already P's trace
... | just P'  | nothing  | refl =
    inj₁ (_ , bStep (sVis p-eq fp-eq) big-step)

-- nothing / just Q' → mergeVis = just Q', eq-j : just Q' ≡ just t'
... | nothing  | just Q'  | refl =
    inj₂ (_ , bStep (sVis q-eq fq-eq) big-step)

-- just P' / just Q' → mergeVis = just (P' □ Q'), big-step : (P' □ Q') ═⟨ s ⟩═► _
... | just P'  | just Q'  | refl =
    case InternalChoice-trace P' Q' (_ , big-step) of λ where
      (inj₁ (t-end , trP)) → inj₁ (t-end , bStep (sVis p-eq fp-eq) trP)
      (inj₂ (t-end , trQ)) → inj₂ (t-end , bStep (sVis q-eq fq-eq) trQ)

-- nothing / nothing → mergeVis = nothing, eq-j : nothing ≡ just t' — impossible
... | nothing  | nothing  | ()

-- These cases are impossible because (ret □ ret)
--------------------------------------------------------------------------------------
-- For the "ret r1" and "ret r2" case, it is a bit complicated because the definition
-- of □ relies on a Dec to reduce it to "ret r1" if r1 = r2, or Stop otherwise.
-- Stop is "vis (λ _ _ → nothing)", and so we need to prove Stop is not possible for sVis

ExternalChoice-trace {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ with r1 ≟ r2
-- match with r1 ≟ r2: yes
...                     | yes refl rewrite p-eq | q-eq with r1 ≟ r1
-- match with r1 ≟ r1: yes
...                                                     | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ | _
-- match with r1 ≟ r1: no    
                                                        | no neq with eq-f -- {!!} -- with eq-f
...                                                               | ()

ExternalChoice-trace {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _
-- match with r1 ≟ r2: no    
                       | no neq rewrite p-eq | q-eq with r1 ≟ r2
-- match the 2nd with r1 ≟ r2 : yes
...                                                    | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ | _
-- match the 2nd with r1 ≟ r2 : no  
                                                       | no neq with eq-f
...                                                              | ()

--------------------------------------------------------------------------------------

ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _  | vis _  | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis _  | ret _  | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis _  | ndbr _ _ _ _ | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ndbr _ _ _ _ | vis _  | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _  | ndbr _ _ _ _ | ()
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ndbr _ _ _ _ | ret _  | ()

-- 4. Termination (sRet)
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = √ r} (sRet eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq
-- Case: Both P and Q are ready to terminate
... | ret r1 | ret r2 with r1 ≟ r2
-- Branch: They agree (r1 ≡ r2)
... | yes refl = 
    case eq-f of λ where
      refl → -- This unifies r1 with r
        inj₁ (_ , bStep (sRet p-eq) big-step) -- Or inj₂, both work!

-- Branch: They disagree (r1 ≢ r2)
-- The definition says this results in 'Stop'. 
-- Stop cannot perform an 'sRet' step, so this case is impossible.
... | no  neq = 
    case eq-f of λ where 
      () -- force (P □ Q) is Stop, which != ret r

-- Case: P terminates, Q is offering something else (vis or ndbr)
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = √ r} (sRet eq-f) big-step) | ret r1 | vis fQ = 
    case eq-f of λ where
      refl → inj₁ (_ , bStep (sRet p-eq) big-step)

ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = √ r} (sRet eq-f) big-step) | ret r1 | ndbr fQ wi wa wp = 
    case eq-f of λ where
      refl → inj₁ (_ , bStep (sRet p-eq) big-step)

-- Case: Q terminates, P is offering something else
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = √ r} (sRet eq-f) big-step) | vis fP | ret r2 = 
    case eq-f of λ where
      refl → inj₂ (_ , bStep (sRet q-eq) big-step)

ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bStep {el = √ r} (sRet eq-f) big-step) | ndbr fP wi wa wp | ret r2 = 
    case eq-f of λ where
      refl → inj₂ (_ , bStep (sRet q-eq) big-step)

-- 5. Case: Non-deterministic branching (ndbr)
-- If P is an ndbr, the whole choice becomes an ndbr of (Pi □ Q).
-- eq-f: ITree.force p ≡ ndbr f wi wa prf 
-- eq-j: f i a ≡ just t′
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) 
  with P .force in p-eq | Q .force in q-eq | eq-f
-- 5.1. Case: P is vis, Q is ndbr
-- Definition uses: fQ' i a = just (P □ Q')
... | vis fP | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl = 
    case ExternalChoice-trace P Q' (_ , big-step) of λ where
      (inj₁ trP) → inj₁ trP
      (inj₂ (t'' , trQ)) → inj₂ (t'' , bTau (sNdbr q-eq fq-eq) trQ)
-- If the branch is nothing, eq-j (which is fQ' i a ≡ just t') is impossible
... | nothing | ()

-- 5.2. Case: P is ndbr, Q is vis
-- Definition uses: fP' i a = just (P' □ Q)
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | vis fQ | refl with fP i a in fp-eq | eq-j
... | just P' | refl = 
    case ExternalChoice-trace P' Q (_ , big-step) of λ where
      (inj₁ (t'' , trP)) → inj₁ (t'' , bTau (sNdbr p-eq fp-eq) trP)
      (inj₂ trQ) → inj₂ trQ      
-- If the branch is nothing, eq-j (which is fQ' i a ≡ just t') is impossible
... | nothing | ()

-- 5.3. Case: Both are ndbr (The mergeNdbr rule)
-- eq-f  : ITree.force (P □ Q) ≡ ndbr (mergeNdbr fP fQ) ((AP×AQ, pair iP iQ)) (waP,waQ) go-prf
-- eq-j  : (mergeNdbr fP fQ) i a ≡ just t′
-- i, a  : the branch actually taken inside (P □ Q)
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (t'' , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP (AP , iP) waP wpP | ndbr fQ (AQ , iQ) waQ wpQ | refl
  -- i must be a pair index for mergeNdbr to give `just`; case on it:
  with i | a 
-- i is a base or fin index → mergeNdbr returns nothing → eq-j is impossible
... | (_ , base _) | _ = case eq-j of λ ()
... | (_ , fin)    | _ = case eq-j of λ ()
-- i is a pair index: i = (AP' × AQ' , pair iP' iQ'), a = (aP' , aQ')
... | (.(AP' × AQ') , pair {AP'} {AQ'} iP' iQ') | (aP' , aQ') 
  -- now case-split on fP (AP', iP') aP' and fQ (AQ', iQ') aQ'
  with fP (AP' , iP') aP' in fp'-eq | fQ (AQ' , iQ') aQ' in fq'-eq | eq-j
-- just P' / nothing → mergeNdbr = just P', so eq-j : just P' ≡ just t''
... | just P' | nothing | refl =
    inj₁ (_ , bTau (sNdbr p-eq fp'-eq) big-step)
    {-case ExternalChoice-trace P' Q (_ , big-step) of λ where
      (inj₁ (t-end , trP)) → inj₁ (t-end , bTau (sNdbr p-eq fp'-eq) trP)
      (inj₂ trQ) → inj₂ trQ
    -}
-- nothing / just Q' → mergeNdbr = just Q', so eq-j : just Q' ≡ just t''
... | nothing  | just Q'  | refl =
    inj₂ (_ , bTau (sNdbr q-eq fq'-eq) big-step)
    {-
    case ExternalChoice-trace P Q' (_ , big-step) of λ where
      (inj₁ trP)           → inj₁ trP
      (inj₂ (t-end , trQ)) → inj₂ (t-end , bTau (sNdbr q-eq fq'-eq) trQ)
    -}
-- just P' / just Q' → mergeNdbr = just (P' □ Q'), so eq-j : just (P' □ Q') ≡ just t''
... | just P'  | just Q'  | refl =
    case ExternalChoice-trace P' Q' (_ , big-step) of λ where
      (inj₁ (t-end , trP)) → inj₁ (t-end , bTau (sNdbr p-eq fp'-eq) trP)
      (inj₂ (t-end , trQ)) → inj₂ (t-end , bTau (sNdbr q-eq fq'-eq) trQ)
-- nothing / nothing → mergeNdbr = nothing, so eq-j : nothing ≡ just t'' — impossible
... | nothing  | nothing  | ()
-- ExternalChoice-trace {I = I} {R = R} {s = s} P Q (t'' , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
--  | _ | _ |  ()

-- 5.4. If P is silent, the choice takes an sSil step, not sNdbr.
ExternalChoice-trace P Q (t'' , bTau (sNdbr eq-f eq-j) big-step) 
  | sil P' | _ | ()

-- 5.5. If P is stable but Q is silent, the choice takes an sSil step.
ExternalChoice-trace P Q (t'' , bTau (sNdbr eq-f eq-j) big-step) 
  | ret _ | sil Q' | ()
ExternalChoice-trace P Q (t'' , bTau (sNdbr eq-f eq-j) big-step) 
  | vis _ | sil Q' | ()
ExternalChoice-trace P Q (t'' , bTau (sNdbr eq-f eq-j) big-step) 
  | ndbr _ _ _ _ | sil Q' | ()

-- 5.6. Both ready to terminate
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) 
  | ret r1 | ret r2 | _ with r1 ≟ r2
-- Case: They agree. force (P □ Q) reduces to (ret r1)
-- Agda sees: (ret r1 ≡ ndbr ...) which is clearly impossible.
... | yes refl rewrite p-eq | q-eq with r1 ≟ r1
-- match with r1 ≟ r1: yes
...                                                     | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) 
  | ret r1 | ret r2 | _ | _
-- match with r1 ≟ r1: no    
                                                        | no neq = ⊥-elim (neq refl)

-- Case: They disagree. force (P □ Q) reduces to (Stop .force)
-- Agda sees: (Stop .force ≡ ndbr ...) which is also impossible.
ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _
-- match with r1 ≟ r2: no    
                       | no neq rewrite p-eq | q-eq with r1 ≟ r2
-- match the 2nd with r1 ≟ r2 : yes
...                                                    | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace {I = I} {R = R} {s = s} P Q (._ , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ | _
-- match the 2nd with r1 ≟ r2 : no  
                                                         | no neq with eq-f
...                                                                | refl with i | a | eq-j
-- i must be fin-indexed for br2 to return just
...                                                                            | (_ , fin) | lift fzero        | refl = inj₁ (_ , big-step)
...                                                                            | (_ , fin) | lift (fsuc fzero) | refl = inj₂ (_ , big-step)
-- all other fin cases return nothing, so eq-j : nothing ≡ just t′ is impossible
...                                                                            | (_ , fin) | lift (fsuc (fsuc _)) | ()
-- base and pair cases also return nothing
...                                                                            | (_ , base _)    | _ | ()
...                                                                            | (_ , pair _ _)  | _ | ()

-- 5.7. 
ExternalChoice-trace P Q (t'' , bTau (sNdbr eq-f eq-j) big-step) 
  | ret _ | vis _ | ()

-- 5.8. 
ExternalChoice-trace P Q (t'' , bTau (sNdbr eq-f eq-j) big-step) 
  | vis _ | ret _ | ()

-----------------------------------------------------------------------------------------
-- Bind >>=
-- traces [P >>= Q] =
-- traces [P ; Q] = {trp : traces [P] | ✓ ∉ trp • trp } ∪
--                  {trp : traces [P] ; trq : traces [Q] | ✓ ∉ trp ∧ trp ⌢ ⟨✓⟩ ∈ traces [P] • trp ⌢ trq }

data BindSplit {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E I R) (k : R → ITree E I S) (t-final : ITree E I S)
  : List (Event√ E S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where
  -- Case 1: P is still executing
  in-P : ∀ {P'} {s : List (Event E)}
       -- We lift plain events s into Event√ E S to match the bind's trace
       → traces P (map evl s)              
       → t-final ≡ (P' >>= k)
       → BindSplit P k t-final (map evl s)

  -- Case 2: P finished and we transitioned to k
  in-k : ∀ {s : List (Event√ E S)} 
       → (r : R) 
       → (s1 : List (Event E))            -- Plain events from P
       → (s2 : List (Event√ E S))         -- Full trace from k (can include √ S)
       → (s ≡ map evl s1 ++ s2)            -- s1 is lifted to S-type to join s2
       → traces P (map evl s1 ++ [ √ r ])  -- s1 is lifted to R-type to match P
       → traces (k r) s2                  -- Already S-type
       → BindSplit P k t-final s


-- A helper to allow us induct on transition directly, instead of 
bind-trace-helper : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
   (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
   {s : List (Event√ E S)} (t-f : ITree E (ExtI I) S)
   → (P >>= k) ═⟨ s ⟩═► t-f    -- The transition proof is now isolated!
   → Σ (ITree E (ExtI I) S) (λ t-f' → BindSplit P k t-f' s)

-- Base Case
bind-trace-helper P k t-f bNil = t-f , in-P (P , bNil) refl

-- 1. Handling Silent Steps (Tau via sSil)
bind-trace-helper P k t-f (bTau (sSil {t = next} eq-f) big-step) with P .force in p-eq | eq-f
... | sil c | refl =
    -- Recurse using the helper, passing t-f and big-step separately
    case bind-trace-helper c k t-f big-step of λ where
      (tend , in-P (P' , c-step) eq) → 
          tend , in-P (P' , bTau (sSil p-eq) c-step) eq
      (tend , in-k r s1 s2 eq-s (P' , c-step) trk2) → 
          tend , in-k r s1 s2 eq-s (P' , bTau (sSil p-eq) c-step) trk2

... | ret r' | eq-f' = 
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bTau (sSil eq-f') big-step)

... | vis _        | ()
... | ndbr _ _ _ _ | ()

-- 2. Handling Non-deterministic Steps (Tau via sNdbr)
bind-trace-helper P k t-f (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | ndbr f wi wa wp | refl with f i a in fi-eq | eq-j
... | just P' | refl =
    -- Recurse using the helper, passing t-f and big-step separately
    case bind-trace-helper P' k t-f big-step of λ where
      
      (tend , in-P (P'' , c-step) eq) → 
          tend , in-P (P'' , bTau (sNdbr p-eq fi-eq) c-step) eq
          
      (tend , in-k r s1 s2 eq-s (P'' , c-step) trk2) → 
          tend , in-k r s1 s2 eq-s (P'' , bTau (sNdbr p-eq fi-eq) c-step) trk2
          
... | nothing | ()

-- The Hand-off case
bind-trace-helper P k t-f (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) 
    | ret r' | eq-f' = 
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bTau (sNdbr eq-f' eq-j) big-step)

-- Absurd cases (updated to the curried helper format)
bind-trace-helper P k t-f (bTau (sNdbr eq-f eq-j) big-step) | sil _ | ()
bind-trace-helper P k t-f (bTau (sNdbr eq-f eq-j) big-step) | vis _ | ()

-- 3. Handling Visible Steps (e via sVis)
bind-trace-helper P k t-f (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | vis f | refl with f at a in fi-eq | eq-j
... | just P' | refl =
    -- Recurse using the helper, passing t-f and big-step separately
    case bind-trace-helper P' k t-f big-step of λ where
      
      (tend , in-P {s = sP} (P'' , c-step) eq) → 
          tend , in-P {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP} (P'' , bStep (sVis p-eq fi-eq) c-step) eq
          
      (tend , in-k r s1 s2 eq-s (P'' , c-step) trk2) → 
          tend , in-k r ((evLabel (proj₁ at) (proj₂ at) a) ∷ s1) s2 (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (P'' , bStep (sVis p-eq fi-eq) c-step) trk2
          
... | nothing | ()

-- The Hand-off case
bind-trace-helper P k t-f (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step) 
    | ret r' | eq-f' = 
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bStep (sVis eq-f' eq-j) big-step)

-- Absurd cases (updated to the curried helper format)
bind-trace-helper P k t-f (bStep (sVis eq-f eq-j) big-step) | sil _        | ()
bind-trace-helper P k t-f (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()

-- 4. Handling Termination (The hand-off to k via sRet)
bind-trace-helper P k t-f (bStep (sRet {x = r} eq-f) big-step) with P .force in p-eq | eq-f
... | ret r' | eq-f' = 
    -- Hand-off point: s1 is empty ([]). P's trace is done. 
    -- The rest of the transition (big-step) belongs to (k r').
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bStep (sRet eq-f') big-step)

-- Absurd cases (updated to the curried helper format)
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | sil _        | ()
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | vis _        | ()
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ()

bind-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
   (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
   {s : List (Event√ E S)}
   → traces (P >>= k) s
   → Σ (ITree E (ExtI I) S) (λ t-f → BindSplit P k t-f s)
-- By moving the logic into the helpfer function, we can overcome the termination
-- checking error for the below version. 
bind-trace P k (t-f , tr) = bind-trace-helper P k t-f tr

{-
-- {-# NON_TERMINATING #-}
bind-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
   (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
   {s : List (Event√ E S)}
   → traces (P >>= k) s
   → Σ (ITree E (ExtI I) S) (λ t-f → BindSplit P k t-f s)

-- Base Case
bind-trace P k (t-f , bNil) = t-f , in-P (P , bNil) refl

-- ==========================================
-- 1. Handling Silent Steps (Tau via sSil)
-- ==========================================
bind-trace P k (t-f , bTau (sSil {t = next} eq-f) big-step) with P .force in p-eq | eq-f
... | sil c | refl =
-- ====================================================================
-- This causes the termination checking error because the termination checker
-- cannot see that big-step is smaller than bTau (sSil eq-f) big-step when
-- c is not syntactically a subterm of P. The recursive call bind-trace c k
-- (t-f , big-step) is fine on the trace argument, but Agda's termination
-- checker needs a lexicographic measure and loses track when with P .force.
--
-- The core issue is that with P .force in p-eq abstracts over P .force,
-- which hides the structural relationship between P and c from the termination
-- checker. It can no longer see that big-step is a strict subterm of the
-- original trace.
--
-- Solution:  Induct on the trace proof directly
-- ====================================================================
    -- 1. Recurse on 'c', because P stepped to c!
    case bind-trace c k (t-f , big-step) of λ where
      
      -- 2. Deconstruct the trace pair (P' , c-step)
      (tend , in-P (P' , c-step) eq) → 
          -- 3. Reconstruct the trace pair for P using P' and the new bTau
          tend , in-P (P' , bTau (sSil p-eq) c-step) eq
      
      -- Do the same for in-k. trP1 is a pair (P' , c-step)
      (tend , in-k r s1 s2 eq-s (P' , c-step) trk2) → 
          tend , in-k r s1 s2 eq-s (P' , bTau (sSil p-eq) c-step) trk2

... | ret r' | eq-f' = 
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bTau (sSil eq-f') big-step)
... | vis _        | ()
... | ndbr _ _ _ _ | ()

-- ==========================================
-- 2. Handling Non-deterministic Steps (Tau via sNdbr)
-- ==========================================
-- Notice we explicitly bind `eq-j` here so it is in scope for the `with` block
bind-trace P k (t-f , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | ndbr f wi wa wp | refl with f i a in fi-eq | eq-j
... | just P' | refl =
    case bind-trace P' k (t-f , big-step) of λ where
      
      -- 1. Destructure into (P'' , c-step)
      (tend , in-P (P'' , c-step) eq) → 
          tend , in-P (P'' , bTau (sNdbr p-eq fi-eq) c-step) eq
          
      (tend , in-k r s1 s2 eq-s (P'' , c-step) trk2) → 
          tend , in-k r s1 s2 eq-s (P'' , bTau (sNdbr p-eq fi-eq) c-step) trk2
          
-- The branch f i a returning 'nothing' contradicts eq-j : just t' ≡ nothing
... | nothing | ()
-- Absurd cases for sNdbr
bind-trace P k (t-f , bTau (sNdbr eq-f eq-j) big-step) | sil _ | ()
bind-trace P k (t-f , bTau (sNdbr eq-f eq-j) big-step)
    | ret r' | eq-f' = 
      t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bTau (sNdbr eq-f' eq-j) big-step)

bind-trace P k (t-f , bTau (sNdbr eq-f eq-j) big-step) | vis _ | ()

-- ==========================================
-- 3. Handling Visible Steps (e via sVis)
-- ==========================================
bind-trace P k (t-f , bStep (sVis {at = at} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | vis f | refl with f at a in fi-eq | eq-j
... | just P' | refl =
-- Make sure to recurse on P', as the process stepped to P'
    case bind-trace P' k (t-f , big-step) of λ where
      
      -- 1. Bind the implicit {s = sP} so we can use it, and destructure the pair
      (tend , in-P {s = sP} (P'' , c-step) eq) → 
          -- Prepend the visible event to sP, and rebuild the pair for P
          tend , in-P {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP} (P'' , bStep (sVis p-eq fi-eq) c-step) eq
          
      -- 2. Destructure the trace pair into (P'' , c-step)
      (tend , in-k r s1 s2 eq-s (P'' , c-step) trk2) → 
          -- Prepend to s1, KEEP the cong logic, and rebuild the pair for P
          tend , in-k r ((evLabel (proj₁ at) (proj₂ at) a) ∷ s1) s2 (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (P'' , bStep (sVis p-eq fi-eq) c-step) trk2
          
... | nothing | ()
-- Absurd cases for sVis
bind-trace P k (t-f , bStep (sVis eq-f eq-j) big-step) | sil _ | ()
bind-trace P k (t-f , bStep (sVis eq-f eq-j) big-step)
-- The hand-off: P returned, so this visible step actually belongs to k!
    | ret r' | eq-f' = 
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bStep (sVis eq-f' eq-j) big-step)
bind-trace P k (t-f , bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()

-- ==========================================
-- 4. Handling Termination (The hand-off to k via sRet)
-- ==========================================
bind-trace P k (t-f , bStep (sRet {x = r} eq-f) big-step) with P .force in p-eq | eq-f
... | ret r' | eq-f' = 
    -- Hand-off point: s1 is empty ([]). P's trace is done. 
    -- The rest of the transition (big-step) belongs to (k r').
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bStep (sRet eq-f') big-step)
-- Absurd cases for sRet
bind-trace P k (t-f , bStep (sRet eq-f) big-step) | sil _        | ()
bind-trace P k (t-f , bStep (sRet eq-f) big-step) | vis _        | ()
bind-trace P k (t-f , bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ()
-}

-----------------------------------------------------------------------------------------
-- Bind >>

data Bind₀Split {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E I R) (Q : ITree E I S) (t-final : ITree E I S)
  : List (Event√ E S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where
  -- Case 1: P is still executing
  in-P₀ : ∀ {P'} {s : List (Event E)}
       -- We lift plain events s into Event√ E S to match the bind's trace
       → traces P (map evl s)              
       → t-final ≡ (_>>_ {R = R} P' Q)
       → Bind₀Split P Q t-final (map evl s)

  -- Case 2: P finished and we transitioned to k
  in-Q₀ : ∀ {s : List (Event√ E S)} 
       → (r : R) 
       → (s1 : List (Event E))            -- Plain events from P
       → (s2 : List (Event√ E S))         -- Full trace from k (can include √ S)
       → (s ≡ map evl s1 ++ s2)            -- s1 is lifted to S-type to join s2
       → traces P (map evl s1 ++ [ √ r ])  -- s1 is lifted to R-type to match P
       → traces Q s2                  -- Already S-type
       → Bind₀Split P Q t-final s

bind₀-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
   {s : List (Event√ E S)}
   (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
   → traces (P >> Q) s
   → Σ (ITree E (ExtI I) S) (λ t-f → Bind₀Split P Q t-f s)
bind₀-trace {ℓr = ℓr} {R = R} {s = s} P Q tr =
  let (t-f , bsplit) = bind-trace P (λ _ → Q) tr
  in t-f , help bsplit
    where
      help : ∀ {t-f} → BindSplit {ℓr = ℓr} {R = R} P (λ _ → Q) t-f _ → Bind₀Split P Q t-f _
      -- We explicitly name P' here to help unification
      help (in-P {P' = P'} sP trP) = 
        in-P₀ {P' = P'} sP trP
        
      help (in-k r s1 s2 eq trP trQ) = 
        in-Q₀ r s1 s2 eq trP trQ

-----------------------------------------------------------------------------------------
-- Kleisli composition >=> or ⨾

data KleisliSplit {ℓi ℓr ℓs ℓt} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs} {T : Set ℓt}
  (P : KTree E (ExtI I) R S) (Q : KTree E (ExtI I) S T) (x : R) (t-final : ITree E (ExtI I) T)
  : List (Event√ E T) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs ⊔ ℓt) where

  in-Pᵏ : ∀ {P'} {s : List (Event E)}
       → traces (P x) (map evl s)
       → t-final ≡ (P' >>= Q)
       → KleisliSplit P Q x t-final (map evl s)

  in-Qᵏ : ∀ {s : List (Event√ E T)} 
       → (r : S) (s1 : List (Event E)) (s2 : List (Event√ E T))
       → (s ≡ map evl s1 ++ s2)
       → traces (P x) (map evl s1 ++ [ √ r ])
       → traces (Q r) s2
       → KleisliSplit P Q x t-final s

kleisli-trace : ∀ {ℓi ℓr ℓs ℓt} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs} {T : Set ℓt}
  {s : List (Event√ E T)} (x : R)
  (P : KTree E (ExtI I) R S) (Q : KTree E (ExtI I) S T)
  → traces ((P >=> Q) x) s
  → Σ (ITree E (ExtI I) T) (λ t-f → KleisliSplit P Q x t-f s)
kleisli-trace {S = S} {T = T} {s = s} x P Q tr = 
  -- We leverage the bind-trace lemma we already finished
  let (t-f , bsplit) = bind-trace (P x) Q tr 
  in t-f , help bsplit
  where
    -- Helper to solve the UnsolvedConstraints for S and T (the return types)
    help : ∀ {t-f} → BindSplit {R = S} {S = T} (P x) Q t-f s → KleisliSplit P Q x t-f s
    
    -- Case 1: P x is still running
    help (in-P {P' = P'} sP trP) = 
      in-Pᵏ sP trP
      
    -- Case 2: P x finished with result 'r', and Q r took over
    help (in-k r s1 s2 eq trP trQ) = 
      in-Qᵏ r s1 s2 eq trP trQ


-----------------------------------------------------------------------------------------
-- Sliding : P ▷ Q

sliding-trace-helper : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ dec : DecEq R ⦄
  {s : List (Event√ E R)}
   (P Q : ITree E (ExtI I) R) (t-f : ITree E (ExtI I) R)
   → (P ▷ Q) ═⟨ s ⟩═► t-f 
   → traces P s ⊎ traces Q s

-- Base Case
sliding-trace-helper P Q t-f bNil = inj₁ (P , bNil)

-- 1. Silent Step: sSil
sliding-trace-helper P Q t-f (bTau (sSil eq) big-step) with P .force in eq-P | eq
... | ret r | ()  -- Agda now sees `ret r ≡ sil t'`, which is absurd!
... | sil P' | refl = 
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sSil eq-P) trP')
      (inj₂ trQ)           → inj₂ trQ
... | vis fP | eq-sil = 
    case InternalChoice-trace (P □ Q) Q (t-f , bTau (sSil eq-sil) big-step) of λ where
      (inj₁ trExt) → ExternalChoice-trace P Q trExt
      (inj₂ trQ)   → inj₂ trQ
... | ndbr fP wi wa wp | eq-sil = 
    case InternalChoice-trace (P □ Q) Q (t-f , bTau (sSil eq-sil) big-step) of λ where
      (inj₁ trExt) → ExternalChoice-trace P Q trExt
      (inj₂ trQ)   → inj₂ trQ

-- 2. Silent Step: sNdbr
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) with P .force in eq-P | eq
... | ret r | ()
... | sil P' | () -- sil ≡ ndbr is absurd
... | vis fP | eq-ndbr = 
    case InternalChoice-trace (P □ Q) Q (t-f , bTau (sNdbr eq-ndbr eq-j) big-step) of λ where
      (inj₁ trExt) → ExternalChoice-trace P Q trExt
      (inj₂ trQ)   → inj₂ trQ
... | ndbr fP wi wa wp | eq-ndbr = 
    case InternalChoice-trace (P □ Q) Q (t-f , bTau (sNdbr eq-ndbr eq-j) big-step) of λ where
      (inj₁ trExt) → ExternalChoice-trace P Q trExt
      (inj₂ trQ)   → inj₂ trQ

-- 3. Visible Step: sVis
sliding-trace-helper P Q t-f (bStep (sVis eq eq-j) big-step) with P .force in eq-P | eq
... | ret r | ()
... | sil P' | ()
... | vis fP | eq-vis = 
    case InternalChoice-trace (P □ Q) Q (t-f , bStep (sVis eq-vis eq-j) big-step) of λ where
      (inj₁ trExt) → ExternalChoice-trace P Q trExt
      (inj₂ trQ)   → inj₂ trQ
... | ndbr fP wi wa wp | eq-vis = 
    case InternalChoice-trace (P □ Q) Q (t-f , bStep (sVis eq-vis eq-j) big-step) of λ where
      (inj₁ trExt) → ExternalChoice-trace P Q trExt
      (inj₂ trQ)   → inj₂ trQ

-- 4. Visible Step: sRet
sliding-trace-helper P Q t-f (bStep (sRet eq) big-step) with P .force in eq-P | eq
... | ret r | refl = 
    -- If P ▷ Q successfully returns, it's because P successfully returned!
    -- We can hand this straight back to P.
    inj₁ (t-f , bStep (sRet eq-P) big-step)
... | sil P' | ()
... | vis fP | eq-ret = 
    case InternalChoice-trace (P □ Q) Q (t-f , bStep (sRet eq-ret) big-step) of λ where
      (inj₁ trExt) → ExternalChoice-trace P Q trExt
      (inj₂ trQ)   → inj₂ trQ
... | ndbr fP wi wa wp | eq-ret = 
    case InternalChoice-trace (P □ Q) Q (t-f , bStep (sRet eq-ret) big-step) of λ where
      (inj₁ trExt) → ExternalChoice-trace P Q trExt
      (inj₂ trQ)   → inj₂ trQ
      
Sliding-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ dec : DecEq R ⦄
  (P Q : ITree E (ExtI I) R) {s : List (Event√ E R)}
  → traces {I = ExtI I} {R = R} (_▷_ {I = I} {R = R} P Q) s
  → traces P s ⊎ traces Q s
Sliding-trace P Q (t-f , tr) = sliding-trace-helper P Q t-f tr  

-----------------------------------------------------------------------------------------
-- iter-bind

-- Specifically for iter-bind, similar to bindSplit or iterSplit
data IterGBindSplit {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (c : ITree E (ExtI I) (A ⊎ R)) (body : A → ITree E (ExtI I) (A ⊎ R))
  (t-final : ITree E (ExtI I) R)
  : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  -- Case 1: c is still executing
  in-c : ∀ {c'} {s : List (Event E)}
       → traces c (map evl s)
       → t-final ≡ iter-bind c' body
       → IterGBindSplit c body t-final (map evl s)

  -- Case 2: c finished with inj₁ a', handing control directly to the loop.
  in-loop' : ∀ {a' : A} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → (s ≡ map evl s1 ++ s2)            
       → traces c (map evl s1 ++ [ √ (inj₁ a') ]) 
       → traces (iter body a') s2
       → IterGBindSplit c body t-final s

  -- Case 3: c finished with inj₂ r, finalizing the result.
  in-done' : ∀ {r : R} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → (s ≡ map evl s1 ++ s2)            
       → traces c (map evl s1 ++ [ √ (inj₂ r) ]) 
       → traces {I = ExtI I} (Ret r) s2     
       → IterGBindSplit c body t-final s

-- A helper to allow us to induct on the transition directly for iter-bind
iter-bind-trace-helper : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (c : ITree E (ExtI I) (A ⊎ R)) (body : A → ITree E (ExtI I) (A ⊎ R))
   {s : List (Event√ E R)} (t-f : ITree E (ExtI I) R)
   → iter-bind c body ═⟨ s ⟩═► t-f 
   → Σ (ITree E (ExtI I) R) (λ t-f' → IterGBindSplit c body t-f' s)

-- Base Case
iter-bind-trace-helper c body t-f bNil = t-f , in-c (c , bNil) refl

-- 1. Handling Silent Steps (Tau via sSil)
iter-bind-trace-helper c body t-f (bTau (sSil {t = next} eq-f) big-step) with c .force in c-eq | eq-f
... | sil c' | refl =
    case iter-bind-trace-helper c' body t-f big-step of λ where
      (tend , in-c (c'' , c-step) eq) → 
          tend , in-c (c'' , bTau (sSil c-eq) c-step) eq
      (tend , in-loop' eq-s (c'' , c-step) trk2) → 
          tend , in-loop' eq-s (c'' , bTau (sSil c-eq) c-step) trk2
      (tend , in-done' eq-s (c'' , c-step) trk2) → 
          tend , in-done' eq-s (c'' , bTau (sSil c-eq) c-step) trk2

... | ret (inj₁ a') | refl = 
    -- iter-bind c body evaluates to sil (iter body a'). 
    -- Matching refl proves `next` is exactly `iter body a'`, 
    -- meaning `big-step` is exactly the trace of `iter body a'`!
    t-f , in-loop' refl (_ , bStep (sRet c-eq) bNil) (t-f , big-step)

... | ret (inj₂ r) | () -- ret ≡ sil is absurd

... | vis _        | ()
... | ndbr _ _ _ _ | ()

-- 2. Handling Non-deterministic Steps (Tau via sNdbr)
iter-bind-trace-helper c body t-f (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) with c .force in c-eq | eq-f
... | ndbr f wi wa wp | refl with f i a in fi-eq | eq-j
... | just c' | refl =
    case iter-bind-trace-helper c' body t-f big-step of λ where
      (tend , in-c (c'' , c-step) eq) → 
          tend , in-c (c'' , bTau (sNdbr c-eq fi-eq) c-step) eq
      (tend , in-loop' eq-s (c'' , c-step) trk2) → 
          tend , in-loop' eq-s (c'' , bTau (sNdbr c-eq fi-eq) c-step) trk2
      (tend , in-done' eq-s (c'' , c-step) trk2) → 
          tend , in-done' eq-s (c'' , bTau (sNdbr c-eq fi-eq) c-step) trk2
... | nothing | ()

-- Absurd cases for sNdbr
iter-bind-trace-helper c body t-f (bTau (sNdbr eq-f eq-j) big-step) | sil _   | ()
iter-bind-trace-helper c body t-f (bTau (sNdbr eq-f eq-j) big-step) | vis _   | ()
iter-bind-trace-helper c body t-f (bTau (sNdbr eq-f eq-j) big-step) | ret (inj₁ _) | ()
iter-bind-trace-helper c body t-f (bTau (sNdbr eq-f eq-j) big-step) | ret (inj₂ _) | ()

-- 3. Handling Visible Steps (e via sVis)
iter-bind-trace-helper c body t-f (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step) with c .force in c-eq | eq-f
... | vis f | refl with f at a in fi-eq | eq-j
... | just c' | refl =
    case iter-bind-trace-helper c' body t-f big-step of λ where
      (tend , in-c {s = sP} (c'' , c-step) eq) → 
          tend , in-c {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP} (c'' , bStep (sVis c-eq fi-eq) c-step) eq
      (tend , in-loop' eq-s (c'' , c-step) trk2) → 
          tend , in-loop' (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (c'' , bStep (sVis c-eq fi-eq) c-step) trk2
      (tend , in-done' eq-s (c'' , c-step) trk2) → 
          tend , in-done' (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (c'' , bStep (sVis c-eq fi-eq) c-step) trk2
... | nothing | ()

-- Absurd cases for sVis
iter-bind-trace-helper c body t-f (bStep (sVis eq-f eq-j) big-step) | sil _        | ()
iter-bind-trace-helper c body t-f (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()
iter-bind-trace-helper c body t-f (bStep (sVis eq-f eq-j) big-step) | ret (inj₁ _) | ()
iter-bind-trace-helper c body t-f (bStep (sVis eq-f eq-j) big-step) | ret (inj₂ _) | ()

-- 4. Handling Termination (sRet)
iter-bind-trace-helper c body t-f (bStep (sRet {x = res} eq-f) big-step) with c .force in c-eq | eq-f
... | ret (inj₂ r) | refl = 
    -- Hand-off point. iter-bind evaluated to `ret r`.
    t-f , in-done' {s1 = []} refl (_ , bStep (sRet c-eq) bNil) (t-f , bStep (sRet refl) big-step)

... | ret (inj₁ a') | () -- sil ≡ ret is absurd

-- Absurd cases for sRet
iter-bind-trace-helper c body t-f (bStep (sRet eq-f) big-step) | sil _        | ()
iter-bind-trace-helper c body t-f (bStep (sRet eq-f) big-step) | vis _        | ()
iter-bind-trace-helper c body t-f (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ()

-----------------------------------------------------------------------------------------
-- iter

data IterSplit {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (body : A → ITree E (ExtI I) (A ⊎ R)) (a : A) (t-final : ITree E (ExtI I) R) 
  : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  -- Case 1: Actively executing `body a`. (Maps to BindSplit.in-P)
  in-body : ∀ {P'} {s : List (Event E)}
       → traces (body a) (map evl s)
       → t-final ≡ iter-bind P' body -- (P' >>= iterStep body)
       → IterSplit body a t-final (map evl s)

  -- Case 2: The body finished with `inj₁ a'`, handing control back to the loop.
  in-loop : ∀ {a' : A} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → (s ≡ map evl s1 ++ s2)
       → traces (body a) (map evl s1 ++ [ √ (inj₁ a') ])
       → traces (Tau (iter body a')) s2
       → IterSplit body a t-final s

  -- Case 3: The body finished with `inj₂ r`, returning the final result.
  in-done : ∀ {r : R} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → (s ≡ map evl s1 ++ s2)
       → traces (body a) (map evl s1 ++ [ √ (inj₂ r) ])
       → traces {I = ExtI I} (Ret r) s2
       → IterSplit body a t-final s

iter-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : A → ITree E (ExtI I) (A ⊎ R)) (a : A)
   {s : List (Event√ E R)}
   → traces (iter body a) s
   → Σ (ITree E (ExtI I) R) (λ t-f → IterSplit body a t-f s)

iter-trace body a (t-f , bNil) = 
    t-f , in-body (body a , bNil) refl

iter-trace body a (t-f , bTau (sSil {t = next} eq-f) big-step) 
    with body a .force in b-eq
... | ret (inj₁ a') with eq-f
...                  | refl  =
    -- Because `body a` returned `inj₁ a'`, the body has completed 
    -- its step and handed control back to the loop. 
    -- This is always an `in-loop` case for `body a`.
    t-f , in-loop refl (_ , bStep (sRet b-eq) bNil) (_ , bTau (sSil refl) big-step)

iter-trace body a (t-f , bTau (sSil {t = next} eq-f) big-step) 
  | ret (inj₂ r) = 
    -- iter body a .force = ret r in this branch, sSil is impossible
    t-f , in-done refl (_ , bStep (sRet b-eq) bNil) (_ , bTau (sSil eq-f) big-step)

iter-trace body a (t-f , bTau (sSil {t = next} eq-f) big-step) 
  | sil c with eq-f
...        | refl = 
    -- iter body a .force = sil (c >>= iterStep body)
    case iter-bind-trace-helper c body t-f big-step of λ where
      (tend , in-c {c' = c'} (c_end , c-step) eq-P) → 
          tend , in-body (c_end , bTau (sSil b-eq) c-step) eq-P

      (tend , in-loop' eq-s (c_end , c-step) (k_end , k-step)) → 
          tend , in-loop eq-s 
              (c_end , bTau (sSil b-eq) c-step) 
              (k_end , bTau (sSil refl) k-step)
              
      (tend , in-done' eq-s (c_end , c-step) trK) → 
          tend , in-done eq-s 
              (c_end , bTau (sSil b-eq) c-step) 
              trK
              
iter-trace body a (t-f , bTau (sSil {t = next} eq-f) big-step) 
  | vis f = 
    -- iter body a .force = vis (...), sSil is impossible here
    case eq-f of λ ()

iter-trace body a (t-f , bTau (sSil {t = next} eq-f) big-step) 
  | ndbr f wi wa wp = 
    case eq-f of λ ()

iter-trace body a (t-f , bTau (sNdbr {i = i} {a = a'} eq-f eq-j) big-step) 
    with body a .force in b-eq
... | ret (inj₁ a'') = case eq-f of λ ()
... | ret (inj₂ r)   = case eq-f of λ ()
... | sil c          = case eq-f of λ ()
... | vis f          = case eq-f of λ ()
... | ndbr f wi wa wp with eq-f
...   | refl with f i a' in fi-eq | eq-j
...     | just t' | refl =
        -- We pass t' and big-step! 
        case iter-bind-trace-helper t' body t-f big-step of λ where
          (tend , in-c (c' , c-step) eq-P) → 
              tend , in-body (c' , bTau (sNdbr b-eq fi-eq) c-step) eq-P
              
          (tend , in-loop' eq-s (c' , c-step) (k_end , k-step)) → 
              tend , in-loop eq-s 
                  (c' , bTau (sNdbr b-eq fi-eq) c-step) 
                  (k_end , bTau (sSil refl) k-step)
                  
          (tend , in-done' eq-s (c' , c-step) trK) → 
              tend , in-done eq-s 
                  (c' , bTau (sNdbr b-eq fi-eq) c-step) 
                  trK
...     | nothing | ()

iter-trace body a (t-f , bStep (sVis {at = at} {a = a'} eq-f eq-j) big-step) 
    with body a .force in b-eq
... | ret (inj₁ a'') = case eq-f of λ ()
... | ret (inj₂ r)   = case eq-f of λ ()
... | sil c          = case eq-f of λ ()
... | ndbr f wi wa wp = case eq-f of λ ()
... | vis f with eq-f
...   | refl with f at a' in fi-eq | eq-j
...     | just t' | refl =
        -- We pass t' and big-step!
        case iter-bind-trace-helper t' body t-f big-step of λ where
          (tend , in-c {s = sP} (c' , c-step) eq-P) → 
              tend , in-body (c' , bStep (sVis b-eq fi-eq) c-step) eq-P
              
          (tend , in-loop' eq-s (c' , c-step) (k_end , k-step)) → 
              tend , in-loop (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a') ∷ xs) eq-s) 
                  (c' , bStep (sVis b-eq fi-eq) c-step) 
                  (k_end , bTau (sSil refl) k-step)
                  
          (tend , in-done' eq-s (c' , c-step) trK) → 
              tend , in-done (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a') ∷ xs) eq-s) 
                  (c' , bStep (sVis b-eq fi-eq) c-step) 
                  trK

iter-trace body a (t-f , bStep (sRet {x = x} eq-f) big-step) 
    with body a .force in b-eq
... | ret (inj₁ a'') = case eq-f of λ ()
... | ret (inj₂ r)   = 
    -- iter body a .force = ret r, sRet step gives x = r
    t-f , in-done {s1 = []} refl 
        (_ , bStep (sRet b-eq) bNil) 
        (_ , bStep (sRet eq-f) big-step)
... | sil c          = case eq-f of λ ()
... | vis f          = case eq-f of λ ()
... | ndbr f wi wa wp = case eq-f of λ ()

