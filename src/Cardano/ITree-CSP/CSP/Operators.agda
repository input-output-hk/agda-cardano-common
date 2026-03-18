{-# OPTIONS --guardedness #-}
-- {-# OPTIONS --safe --without-K #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Fin using (Fin; remQuot) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
-- open import Relation.Unary
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

-- open import Relation.Binary.Definitions using (DecidableEquality)
open import Class.DecEq
open import Level using (Level; 0ℓ)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Interaction_Trees
open import CSP.Basic_Processes

module CSP.Operators {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open ITree

-- Declare first and so they can be defined recursively
Prefix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
       → E A → (A → ITree E (ExtI I) R) → ITree E (ExtI I) R
syntax Prefix ch Px = ch ⟶ Px

Prefix₀ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        → E A → ITree E (ExtI I) R → ITree E (ExtI I) R
syntax Prefix₀ ch Px = ch ⟶₀ Px

-- Guarded process
_＆_ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
     → Bool → ITree E (ExtI I) R → ITree E (ExtI I) R

-- External choice
_□_ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → {{ DecEq R }}
    -- → {{ ClosedI I }}
    → ITree E (ExtI I) R → ITree E (ExtI I) R → ITree E (ExtI I) R

-- Internal / nondeterministic choice
_⊓_ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → ITree E (ExtI I) R → ITree E (ExtI I) R → ITree E (ExtI I) R

-- Sliding (asymmetric) choice
_▷_ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → {{ DecEq R }}
    → ITree E (ExtI I) R → ITree E (ExtI I) R → ITree E (ExtI I) R

-- Sequential composition / monadic bind
_>>=_ : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      → ITree E (ExtI I) R → (R → ITree E (ExtI I) S) → ITree E (ExtI I) S

_>>_ : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
     → ITree E (ExtI I) R → ITree E (ExtI I) S → ITree E (ExtI I) S

-- Kleisli composition
_>=>_ : ∀ {ℓi ℓr ℓs ℓt} {I : Set ℓ → Set ℓi}
          {R : Set ℓr} {S : Set ℓs} {T : Set ℓt}
      → KTree E (ExtI I) R S → KTree E (ExtI I) S T → KTree E (ExtI I) R T

_⨾_ : ∀ {ℓi ℓr ℓs ℓt} {I : Set ℓ → Set ℓi}
        {R : Set ℓr} {S : Set ℓs} {T : Set ℓt}
    → KTree E (ExtI I) R S → KTree E (ExtI I) S T → KTree E (ExtI I) R T
    
-- forget the return of P
forget : ∀ {ℓi ℓr ℓt} {I : Set ℓ → Set ℓi} {R : Set ℓr} → ITree E (ExtI I) R → ITree E (ExtI I) (⊤ {ℓt})
forget P = P >>= (λ _ → Skip)  

infixl 1 _>=>_
infixr 7 Prefix  
infixr 7 Prefix₀

b ＆ P = (guard {ℓr = 0ℓ} b) >> P

-- e?x → P x
-- Prefix : {R : Set} {A : Set} -- → (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
--  → (E A) → (A → ITree E (ExtI I) R) → ITree E (ExtI I) R
force (Prefix {I = I} {A = A} {R = R} e P) = vis cont
  where
    cont : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))
    cont at x with E-≟ (A , e) at
    ... | yes refl = just (P x)
    ... | no  _ = nothing

-- e.x → P
--  Prefix₀ : {R : Set} {A : Set} -- → (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
--    → (E A) → (ITree E (ExtI I) R) → ITree E (ExtI I) R 
Prefix₀ ch Px = Prefix ch (λ _ → Px)

-- trigger is a special version of Prefix which terminates and returns the value taken from the environment
-- it is like ( input?x → ret x )
trigger : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ} → (E A) → ITree E (ExtI I) A
trigger {R} {A} e = e ⟶ (λ x → Ret x)

-- Merge two ITrees
mergeMaybe : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           → Maybe (ITree E (ExtI I) R)
           → Maybe (ITree E (ExtI I) R)
           → Maybe (ITree E (ExtI I) R)
mergeMaybe nothing  nothing  = nothing
mergeMaybe (just p) nothing  = just p
mergeMaybe nothing  (just q) = just q
mergeMaybe (just p) (just q) = just (p ⊓ q)

mergeVis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
         → (A → Maybe (ITree E (ExtI I) R))
         → (A → Maybe (ITree E (ExtI I) R))
         → A → Maybe (ITree E (ExtI I) R)
mergeVis fP fQ x = mergeMaybe (fP x) (fQ x)

-------------------------------------------------------------------------------------
-- External choice
-- We consider more standard version of CSP without ▹, otherwise (P □ Skip = P ▹ Skip)
-- _□_ :  {R : Set} → ITree E (ExtI I) R → ITree E (ExtI I) R → ITree E (ExtI I) R

-- P is τ, P □ Q ⇒ P' □ Q silently, and τ is not kept
force (P □ Q) with P .force | Q .force

-- τ cannot be delayed  
force (P □ Q) | sil P' | _  = sil (P' □ Q)
force (P □ Q) | _ | sil Q'  = sil (P □ Q')  

-- P is ret r.
force (P □ Q) | ret r | ret r' with r ≟ r'
force (P □ Q) | ret r | ret r' | yes refl = ret r
force (P □ Q) | ret r | ret r' | no neq = Stop' .force

force (P □ Q) | ret r | vis _  = ret r
force (P □ Q) | ret r | inv _  = ret r

force (P □ Q) | _ | ret r  = ret r

-- P is vis
-- Merge two partial functions if both are visible.
-- But what about the same events?
-- Merge two functions into one 
force (P □ Q) | vis fP | vis fQ = vis (λ Ae → mergeVis (fP Ae) (fQ Ae))

force (P □ Q) | vis fP | inv fQ = inv (λ ai → λ a →
  case fQ ai a of λ where
    nothing → nothing
    (just Q') → just (P □ Q'))

force (P □ Q) | inv fP | vis fQ = inv (λ ai → λ a →
  case fP ai a of λ where
    nothing → nothing
    (just P') → just (P' □ Q))

-- P is br
{- P1 ⊓ ... ⊓ Pn) □ (Q1 ⊓ ... ⊓ Qm)
≡   (P1 □ Q1) ⊓ ... ⊓ (P1 □ Qm)
  ⊓ (P2 □ Q1) ⊓ ... ⊓ (P2 □ Qm)
  ⊓ ...
  ⊓ (Pn □ Q1) ⊓ ... ⊓ (Pn □ Qm)
-}
-- P = ⨅ i∈I . Pi
-- Q = ⨅ j∈J . Qj
-- P □ Q = ⨅i∈I,j∈J​(Pi​□Qj​)
force (_□_ {I = I} {R = R} P Q) | inv fP | inv fQ = inv mergeInv
  where
    mergeInv : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))
    mergeInv (.(AP × AQ) , pair {AP} {AQ} iP iQ) (aP , aQ) =
      case fP (AP , iP) aP , fQ (AQ , iQ) aQ of λ where
        (just P' , just Q') → just (P' □ Q')   -- ITree E (ExtI I) R ✓
        (just P' , nothing) → just P'
        (nothing , just Q') → just Q'
        (nothing , nothing) → nothing
    mergeInv (A , base i) a = nothing            -- non-pair index: blocked
    mergeInv (_ , fin) a = nothing            -- non-pair index: blocked

-------------------------------------------------------------------------------------
-- Internal choice

--  Definition of ⊓
force (_⊓_ {I = I} {R = R} P Q) = inv br2
  where
    br2 : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))
    br2 (_ , fin) x = case x of λ where
      (lift fzero)        → just P
      (lift (fsuc fzero)) → just Q
      _                   → nothing   -- covers Fin n for n > 2
    br2 (_ , base _)   _ = nothing
    br2 (_ , pair _ _) _ = nothing

-- Prove □ laws
-- Commutativity, idempotence, Associativity

-------------------------------------------------------------------------------------
-- Sliding or asymmetric choice operator, or sometime called untimed time-out operator
-- See TPC and UCS for more details
-- 
-- P ▷ Q = (P ⊓ Stop') □ Q = (P □ Q) ⊓ Q
-- Equal in denotational semantics, but not in operational semantics
-- For an event a in P (? A → P' where a ∈ A) but not in Q, a will resolve sliding to P'
-- For an event b not in P (? A → P' where a ∉ A) but in Q, b will resolve sliding to Q'
-- For an event c in both P (? A → P' where a ∈ A) but in Q, it is nondeterministic choice between P' and Q'
-- For an event d not in both P (? A → P' where a ∉ A) but in Q, it is impossible (nothing)

-- TODO: is this definition correct?

force (P ▷ Q) with P .force | Q .force

force (P ▷ Q) | sil P' | _  = sil (P' ▷ Q)
force (P ▷ Q) | ret r | _ = ret r
force (P ▷ Q) | vis fP | _ = ((P □ Q) ⊓ Q) .force
force (P ▷ Q) | inv fP | _ = ((P □ Q) ⊓ Q) .force

-------------------------------------------------------------------------------------
-- bind operator
-- {-# TERMINATING #-}
-- _>>=_ : {R S : Set} → ITree E (ExtI I) R → (R → ITree E (ExtI I) S) → ITree E (ExtI I) S
force (t >>= k) with force t
... | ret r   = (k r) .force
... | sil c    = sil (c >>= k)
... | vis f = vis (λ at → λ a → 
   case f at a of λ where
     nothing → nothing
     (just t') → just (t' >>= k))

... | inv f = inv (λ ai → λ i →
  case f ai i of λ where
    nothing → nothing
    (just t') → just (t' >>= k))

-------------------------------------------------------------------------------------
-- sequential composition
P >> Q = P >>= (λ _ → Q)

(P >=> Q) x = P x >>= Q

_⨾_ = _>=>_

{-
The following two versions of definition of iter in terms of >>= are not okay in
agda.
error: [TerminationIssue]
Termination checking failed for the following functions:
  iter
Problematic calls:
  λ { (inj₂ r) → Ret r ; (inj₁ a′) → Tau (iter body a′) }

Agda does not support general guarded corecursion through higher-order functions.
Even though this is logically fine:

This is a known limitation of Agda's productivity checker.

Coq allows the higher-order version because:
- CoFixpoint uses a semantic guardedness criterion
- Guard is syntactically tracked

Agda uses purely syntactic guardedness.
-}

{-
iter body a =
  (body a) >>= λ where
    (inj₂ r)  → Ret r
    (inj₁ a′) → Tau (iter body a′)
-}
{-
iter body x =
  do
    ar ← body x
    case ar of λ
      { (inj₁ a) → Tau (iter body a)
      ; (inj₂ r) → Ret r
      }
-}

mutual
  {-# NON_TERMINATING #-}
  iter : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    → (A → ITree E (ExtI I) (A ⊎ R)) → A → ITree E (ExtI I) R
  force (iter body a) with body a .force
  ... | ret (inj₁ a′) = sil (iter body a′)
  ... | ret (inj₂ r)  = ret r
  ... | sil c         = sil (c >>= iterStep body)
  ... | vis  f        = vis  (λ at a → mapMaybe (λ t' → t' >>= iterStep body ) (f at a))
  ... | inv f         = inv  (λ ai a → mapMaybe (λ t' → t' >>= iterStep body ) (f ai a))

  iterStep : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    → (A → ITree E (ExtI I) (A ⊎ R)) → A ⊎ R → ITree E (ExtI I) R
  force (iterStep body (inj₂ r))  = ret r
  force (iterStep body (inj₁ a')) = sil (iter body a')


