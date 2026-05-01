{-# OPTIONS --guardedness #-}
-- {-# OPTIONS --safe --without-K #-}

open import Prelude
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Fin using (Fin; remQuot) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing; Is-just) renaming (map to mapMaybe)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Empty using (⊥)
open import Data.Unit.Base renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
-- open import Relation.Unary
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

-- open import Relation.Binary.Definitions using (DecidableEquality)
open import Class.DecEq using (DecEq; _≟_)
open import Level using (Level; 0ℓ)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Interaction_Trees
open import CSP.Basic_Processes

module CSP.Operators {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open ITree

-- General prefix
Prefix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
       → E A → (A → ITree E (ExtI I) R) → ITree E (ExtI I) R
syntax Prefix ch Px = ch ⟶ Px   -- \-->

-- Prefix without effect or discard the effect
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
-- _>>=_ : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
--      → ITree E (ExtI I) R → (R → ITree E (ExtI I) S) → ITree E (ExtI I) S

_>>=_ : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      → ITree E I R → (R → ITree E I S) → ITree E I S


_>>_ : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
     → ITree E I R → ITree E I S → ITree E I S

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
trigger {I} {A} e = e ⟶ (λ x → Ret x)

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

mergeNdbr : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} {{ _ : DecEq R }}
  → (fP : (i  : AnyTypes (ExtI I)) → ContinueType i  (Maybe (ITree E (ExtI I) R)))
  → (fQ : (i  : AnyTypes (ExtI I)) → ContinueType i  (Maybe (ITree E (ExtI I) R)))
  → (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))
mergeNdbr fP fQ (.(AP × AQ) , pair {AP} {AQ} iP iQ) (aP , aQ) =
  case fP (AP , iP) aP , fQ (AQ , iQ) aQ of λ where
    (just P' , just Q') → just (_□_ P' Q')   -- ITree E (ExtI I) R ✓
    (just P' , nothing) → just P'
    (nothing , just Q') → just Q'
    (nothing , nothing) → nothing
mergeNdbr fP fQ (A , base i) a = nothing            -- non-pair index: blocked
mergeNdbr fP fQ (_ , fin) a = nothing            -- non-pair index: blocked

-- Witness lemma for `mergeNdbr`: if both operands are `just` at their
-- respective witnesses, then the merged `pair`-indexed branch is also
-- `just`.  Used by rule J of `_□_`'s `force` (ndbr/ndbr).
mergeNdbr-witness : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (fP fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → ∀ {AP AQ iP iQ waP waQ}
  → Is-just (fP (AP , iP) waP)
  → Is-just (fQ (AQ , iQ) waQ)
  → Is-just (mergeNdbr fP fQ ((AP × AQ) , pair iP iQ) (waP , waQ))
mergeNdbr-witness fP fQ {AP} {AQ} {iP} {iQ} {waP} {waQ} pP pQ
  with fP (AP , iP) waP | pP | fQ (AQ , iQ) waQ | pQ
... | just _  | _  | just _  | _  = any-just tt₀
... | just _  | _  | nothing | ()
... | nothing | () | _       | _

-- Rule H continuation (vis/ndbr): given a left process P (the `vis`
-- side) and the right side's `ndbr` continuation `fQ`, bundle each
-- enabled Q-branch with P.
mergeNdbr-vis-L : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → ITree E (ExtI I) R
  → ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))
mergeNdbr-vis-L P fQ i a = case fQ i a of λ where
    nothing    → nothing
    (just Q')  → just (P □ Q')

mergeNdbr-vis-L-witness : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → (fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → ∀ {wi wa}
  → Is-just (fQ wi wa)
  → Is-just (mergeNdbr-vis-L P fQ wi wa)
mergeNdbr-vis-L-witness P fQ {wi} {wa} p with fQ wi wa | p
... | just _  | _  = any-just tt₀
... | nothing | ()

-- Rule I continuation (ndbr/vis): given the left side's `ndbr`
-- continuation `fP` and a right process Q (the `vis` side), bundle each
-- enabled P-branch with Q.
mergeNdbr-vis-R : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → ITree E (ExtI I) R
  → (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))
mergeNdbr-vis-R fP Q i a = case fP i a of λ where
    nothing    → nothing
    (just P')  → just (P' □ Q)

mergeNdbr-vis-R-witness : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → (Q : ITree E (ExtI I) R)
  → ∀ {wi wa}
  → Is-just (fP wi wa)
  → Is-just (mergeNdbr-vis-R fP Q wi wa)
mergeNdbr-vis-R-witness fP Q {wi} {wa} p with fP wi wa | p
... | just _  | _  = any-just tt₀
... | nothing | ()

-- P is τ, P □ Q ⇒ P' □ Q silently, and τ is not kept
force (P □ Q) with P .force | Q .force

-- τ cannot be delayed  
force (P □ Q) | sil P' | _  = sil (P' □ Q)
-- force (P □ Q) | _ | sil Q'  = sil (P □ Q')  
force (P □ Q) | ret _ | sil Q'  = sil (P □ Q')
force (P □ Q) | vis _ | sil Q'  = sil (P □ Q')
force (P □ Q) | ndbr _ _ _ _ | sil Q'  = sil (P □ Q')

-- P is ret r.
-----------------------------------------------------------------------------------
-- This is a design decision about how to deal with this case if r ≠ r'
-- We need to consider
--   1. Closure under hiding. This is the most decisive one.
--   2. Consistency with the CSP laws: □-sym or □-comm, (ret r □ ret r') >>= P etc.
--   3. What kind of model you are building?
--        - a synchronisation mechanism (no observable event → stuck)
--        - or a selection mechanism (no basis for selection → arbitrary).
--   Stop : this is the way that ITree-CSP in Isabelle/HOL takes
--   Internal choice: (ret r ⊓ ret r')
--
-- We decide to use the (ret r ⊓ ret r') option, so the hiding laws are still applicable 
-----------------------------------------------------------------------------------  

force (P □ Q) | ret r | ret r' with r ≟ r'
force (P □ Q) | ret r | ret r' | yes refl = ret r
force (P □ Q) | ret r | ret r' | no neq = (P ⊓ Q) .force -- Stop .force

force (P □ Q) | ret r | vis _  = ret r
force (P □ Q) | ret r | ndbr _ _ _ _  = ret r

-- force (P □ Q) | _ | ret r  = ret r
force (P □ Q) | vis _ | ret r  = ret r
force (P □ Q) | ndbr _ _ _ _ | ret r  = ret r

-- P is vis
-- Merge two partial functions if both are visible.
-- But what about the same events? It is nondeterminisitc choice
-- Merge two functions into one 
force (P □ Q) | vis fP | vis fQ = vis (λ Ae → mergeVis (fP Ae) (fQ Ae))

force (P □ Q) | vis fP | ndbr fQ wi wa wp =
      ndbr (mergeNdbr-vis-L P fQ) wi wa (mergeNdbr-vis-L-witness P fQ wp)

force (P □ Q) | ndbr fP wi wa wp | vis fQ =
      ndbr (mergeNdbr-vis-R fP Q) wi wa (mergeNdbr-vis-R-witness fP Q wp)

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
force (P □ Q) | ndbr fP (AP , iP) waP wpP | ndbr fQ (AQ , iQ) waQ wpQ =
      ndbr (mergeNdbr fP fQ) ((AP × AQ) , pair iP iQ) (waP , waQ)
           (mergeNdbr-witness fP fQ wpP wpQ)

-------------------------------------------------------------------------------------
-- Internal choice

--  Definition of ⊓
force (_⊓_ {I = I} {R = R} P Q) = ndbr (br2 P Q) (Lift _ (Fin 2) , fin) (lift fzero) (any-just tt₀)
-- Prove □ laws
-- Commutativity, idempotence, Associativity

-------------------------------------------------------------------------------------
-- Sliding or asymmetric choice operator, or sometime called untimed time-out operator
-- See TPC and UCS for more details
-- 
-- P ▷ Q = (P ⊓ Stop) □ Q = (P □ Q) ⊓ Q                    -- this is from TPC, but UCS prefers it is a premitive operator
-- (P ⊓ Stop) □ Q :
-- (P □ Q) ⊓ Q : Q becomes available via two different τ paths: the "Timeout" Path
--   (Right τ) and the "External Choice" Path (left τ):
--   The system does τ → (P □ Q). 

-- Equal in denotational semantics, but not in operational semantics
-- For an event a in P (? A → P' where a ∈ A) but not in Q, a will resolve sliding to P'
-- For an event b not in P (? A → P' where a ∉ A) but in Q, b will resolve sliding to Q'
-- For an event c in both P (? A → P' where a ∈ A) but in Q, it is nondeterministic choice between P' and Q'
-- For an event d not in both P (? A → P' where a ∉ A) but in Q, it is impossible (nothing)

-- TODO: is this definition correct?

-- From UCS, there are three combinator rules:
--   R1: (a, a),
--   R2: (·, τ, 2)
--   R3: (√, √)

force (P ▷ Q) with P .force

force (P ▷ Q) | ret r = ret r                   -- R3

-- This actually is not specified in R1-3. We treat this as a τ sliding outside.
-- This means Q may occur timeout after several τs, (not only one τ as original meaning).
-- This makes not strongly bisimilar (because of additional τ), not perfectly fine with
-- weakly bisimilar.
force (P ▷ Q) | sil P'  = sil (P' ▷ Q)
  -- We branch: either P continues its silent work, or we timeout to Q.
  -- ((P' ▷ Q) ⊓ Q) .force

-- 
force (P ▷ Q) | vis fP = ((P □ Q) ⊓ Q) .force


force (P ▷ Q) | ndbr fP wi wa wp = ((P □ Q) ⊓ Q) .force

-------------------------------------------------------------------------------------
-- bind operator
-- _>>=_ : {R S : Set} → ITree E (ExtI I) R → (R → ITree E (ExtI I) S) → ITree E (ExtI I) S
force (_>>=_ {ℓi = ℓi} {ℓr = ℓr} {ℓs = ℓs} {I = I} {R = R} {S = S} t k) with force t
... | ret r   = (k r) .force
... | sil c    = sil (c >>= k)
... | vis f = vis (λ at → λ a → 
   case f at a of λ where
     nothing → nothing
     (just t') → just (t' >>= k))

... | ndbr f wi wa wp = ndbr (λ ai → λ i → f' ai i) wi wa (go wp)
  where
    f' : (ai : AnyTypes I) → (a : proj₁ ai) → Maybe (ITree E I S)
    f' ai a = (case f ai a of λ where
        nothing → nothing
        (just t') → just (t' >>= k))
      
    go : Is-just (f wi wa) → Is-just (f' wi wa)
    go p with f wi wa | p
    ... | just x | _ = any-just tt₀
    ... | nothing | ()
    

-------------------------------------------------------------------------------------
-- sequential composition
P >> Q = P >>= (λ _ → Q)

(P >=> Q) x = P x >>= Q

_⨾_ = _>=>_

{-
{-# NON_TERMINATING #-}
iter : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    → (A → ITree E (ExtI I) (A ⊎ R)) → A → ITree E (ExtI I) R
iter body a =
  (body a) >>= λ where
    (inj₂ r)  → Ret r
    (inj₁ a′) → Tau (iter body a′)
-}

{-
mutual
  {-# NON_TERMINATING #-}
  -- NON_TERMINATING will cause (iter body a) not to be reduced to
  -- (body a >>= iterStep body). So proof will be a problem.
  iter : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      → (A → ITree E (ExtI I) (A ⊎ R)) → A → ITree E (ExtI I) R

  iterStep : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
           → (A → ITree E (ExtI I) (A ⊎ R)) → A ⊎ R → ITree E (ExtI I) R
  iterStep body (inj₂ r)  = Ret r
  iterStep body (inj₁ a′) = Tau (iter body a′)

  -- iter : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  --    → (A → ITree E (ExtI I) (A ⊎ R)) → A → ITree E (ExtI I) R
  force (iter body a) = (body a >>= iterStep body) .force

-}

iter : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  → (A → ITree E (ExtI I) (A ⊎ R))
  → A
  → ITree E (ExtI I) R

-- Similar to bind, but redefine it for the iter logic
-- It satisfies the guardedness
iter-bind : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  → ITree E (ExtI I) (A ⊎ R)
  → (A → ITree E (ExtI I) (A ⊎ R))
  → ITree E (ExtI I) R

force (iter-bind {I = I} {R = R} t k) with t .force
... | ret (inj₁ a′)   = sil (iter k a′)
... | ret (inj₂ r)    = ret r
... | sil c           = sil (iter-bind c k)
-- Avoid to use map or mapMaybe to break guardedness
--    ... | vis f           = vis  (λ at i → mapMaybe (iter-bind body) (f at i))
... | vis f = vis (λ at → λ a → 
  case f at a of λ where
    nothing → nothing
    (just t') → just (iter-bind t' k))

... | ndbr f wi wa wp = ndbr (λ ai → λ i → f' ai i) wi wa (go wp)
  where
    f' : (ai : AnyTypes (ExtI I)) → (a : proj₁ ai) → Maybe (ITree E (ExtI I) R)
    f' ai a = (case f ai a of λ where
        nothing → nothing
        (just t') → just (iter-bind t' k))

    go : Is-just (f wi wa) → Is-just (f' wi wa)
    go p with f wi wa | p
    ... | just x | _ = any-just tt₀
    ... | nothing | ()                                 

iter body a = iter-bind (body a) body
