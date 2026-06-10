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
open import CSP.Definitions.Basic_Processes

module CSP.Definitions.Operators {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
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
-- The visible continuation of `Prefix e P`.  Pulled out of the `where`
-- clause of `force (Prefix …)` so that downstream proofs (e.g.
-- `Prefix-step` in `CSP.Laws.FailuresDivergences`) can name it and feed
-- a known result of `E-≟ (A , e) at` through with-abstraction.
Prefix-cont : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
            → (e : E A) → (A → ITree E (ExtI I) R)
            → (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))
Prefix-cont {A = A} e P at x with E-≟ (A , e) at
... | yes refl = just (P x)
... | no  _    = nothing

-- The branch equation at the matching event index: when `at = (A , e)`
-- the continuation hands back `just (P x)`.  Used by `Prefix-step`.
Prefix-cont-just : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                 → (e : E A) (P : A → ITree E (ExtI I) R) (x : A)
                 → Prefix-cont {I = I} e P (A , e) x ≡ just (P x)
Prefix-cont-just {A = A} e P x with E-≟ (A , e) (A , e)
... | yes refl = refl
... | no  neq  = ⊥-elim (neq refl)
  where open import Data.Empty using (⊥-elim)

force (Prefix e P) = vis (Prefix-cont e P)

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
force (P □ Q) | mix fP P' | sil Q'  = sil (P □ Q')

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

-- According to Fig. 13.4 about the reduction strategy of P □ Q in UCS,
-- (?x : A → P(x)) □ SKIP = (?x : A → P(x)) ▷ SKIP
-- Definitionally `(Q ▷ P).force` with Q=vis fQ, P=ret r reduces to `mix fQ P`;
-- writing the reduced form explicitly so Agda can normalise past the with-abstraction.
force (P □ Q) | ret r | vis fQ = mix fQ P
force (P □ Q) | ret r | ndbr fQ wi wa wp =
      ndbr (mergeNdbr-vis-L P fQ) wi wa (mergeNdbr-vis-L-witness P fQ wp)
-- According to Fig. 13.4 about the reduction strategy of P □ Q in UCS,
-- ((?x : A → P(x)) ▷ P') □ SKIP = (?x : A → P(x)) ▷ (P' □ SKIP)
force (P □ Q) | ret r | mix fQ Q'  = mix fQ (P □ Q')

-- force (P □ Q) | _ | ret r  = ret r
force (P □ Q) | vis fP | ret r = mix fP Q
force (P □ Q) | ndbr fP wi wa wp | ret _ =
      ndbr (mergeNdbr-vis-R fP Q) wi wa (mergeNdbr-vis-R-witness fP Q wp)
force (P □ Q) | mix fP P' | ret r  = mix fP (P' □ Q)

-- P is vis
-- Merge two partial functions if both are visible.
-- But what about the same events? It is nondeterminisitc choice
-- Merge two functions into one 
force (P □ Q) | vis fP | vis fQ = vis (λ Ae → mergeVis (fP Ae) (fQ Ae))

force (P □ Q) | vis fP | ndbr fQ wi wa wp =
      ndbr (mergeNdbr-vis-L P fQ) wi wa (mergeNdbr-vis-L-witness P fQ wp)

-- According to Fig. 13.4 about the reduction strategy of P □ Q in UCS,
-- ((?x : A → P(x)) ▷ P') □ Q = (?x : A → P(x)) ▷ (P' □ Q) 
force (P □ Q) | vis fP | mix fQ Q' = mix fQ (P □ Q')

force (P □ Q) | ndbr fP wi wa wp | vis fQ =
      ndbr (mergeNdbr-vis-R fP Q) wi wa (mergeNdbr-vis-R-witness fP Q wp)

force (P □ Q) | mix fP P' | vis fQ = mix fP (P' □ Q)

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

force (P □ Q) | ndbr fP wi wa wp | mix fQ Q' =
      ndbr (mergeNdbr-vis-R fP Q) wi wa (mergeNdbr-vis-R-witness fP Q wp)

force (P □ Q) | mix fP P' | ndbr fQ wi wa wp =
      ndbr (mergeNdbr-vis-L P fQ) wi wa (mergeNdbr-vis-L-witness P fQ wp)

-- According to Fig. 13.4 about the reduction strategy of P □ Q in UCS,
--   ((?x : A → P(x)) ▷ P') □ Q
-- = { reduction }
--   (?x : A → P(x)) ▷ (P' □ Q)
-- = { where Q is also a mix }
--   (?x : A → P(x)) ▷ (P' □ ((?x : B → Q(x)) ▷ Q'))
-- = { reduction }
--   (?x : A → P(x)) ▷ ((?x : B → Q(x)) ▷ (P' □ Q'))
-- = { ▷-assoc }
--   ((?x : A → P(x)) ▷ (?x : B → Q(x))) ▷ (P' □ Q')
-- = { ▷-combine 13.21 }
--   mergeVis(fP fQ) ▷ (P' □ Q')
force (P □ Q) | mix fP P' | mix fQ Q' = 
      mix (λ Ae → mergeVis (fP Ae) (fQ Ae)) (P' □ Q')
      
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

-- They are equal in the trace model, but not in the failures or failures-divergences.

-- For an event a in P (? A → P' where a ∈ A) but not in Q, a will resolve sliding to P'
-- For an event b not in P (? A → P' where a ∉ A) but in Q, b will resolve sliding to Q'
-- For an event c in both P (? A → P' where a ∈ A) but in Q, it is nondeterministic choice between P' and Q'
-- For an event d not in both P (? A → P' where a ∉ A) but in Q, it is impossible (nothing)

-- TODO: is this definition correct?
-- From TPC, there are three operational rules:
--   R1: P --a--> P'   →   P ▷ Q --a--> P'
--   R2: P --τ--> P'   →   P ▷ Q --τ--> P' ▷ Q
--   R3:               →   P ▷ Q --τ--> Q
-- From UCS, there are three combinator rules:
--   R1: (a, a),
--   R2: (·, τ, 2)
--   R3: (√, √)

-- We should use the operation semantics to define the operator, instead of denotational equivalcen.

-- ⊓ distribution
mergeNdbr▷-L : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → ITree E (ExtI I) R      
  → (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))
mergeNdbr▷-L fP Q i a = case fP i a of λ where
    nothing    → nothing
    (just P')  → just (P' ▷ Q)

mergeNdbr▷-L-witness : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → (Q : ITree E (ExtI I) R)
  → ∀ {wi wa}
  → Is-just (fP wi wa)
  → Is-just (mergeNdbr▷-L fP Q wi wa)
mergeNdbr▷-L-witness fP Q {wi} {wa} p with fP wi wa | p
... | just _  | _  = any-just tt₀
... | nothing | ()    

mergeNdbr▷-R : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → ITree E (ExtI I) R
  → ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))
mergeNdbr▷-R P fQ i a = case fQ i a of λ where
    nothing    → nothing
    (just Q')  → just (P ▷ Q')

mergeNdbr▷-R-witness : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → (fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → ∀ {wi wa}
  → Is-just (fQ wi wa)
  → Is-just (mergeNdbr▷-R P fQ wi wa)
mergeNdbr▷-R-witness P fQ {wi} {wa} p with fQ wi wa | p
... | just _  | _  = any-just tt₀
... | nothing | () 

force (P ▷ Q) with P .force | Q .force
-- if Q is nondeterministic choice, it distributes through ▷
force (P ▷ Q) | _ | ndbr fQ wi wa wp =
  ndbr (mergeNdbr▷-R P fQ) wi wa (mergeNdbr▷-R-witness P fQ wp)

force (P ▷ Q) | ret r | _ = ret r                   -- R3

-- This actually is not specified in R1-3. We treat this as a τ sliding outside.
-- This means Q may occur timeout after several τs, (not only one τ as original meaning).
-- This makes not strongly bisimilar (because of additional τ), not perfectly fine with
-- weakly bisimilar.
force (P ▷ Q) | sil P' | _ = sil (P' ▷ Q)
  -- We branch: either P continues its silent work, or we timeout to Q.
  -- ((P' ▷ Q) ⊓ Q) .force

-- force (P ▷ Q) | vis fP = ((P □ Q) ⊓ Q) .force
-- Ideally, we need to distinguish P being between deadlock and non-deadlock,
--   if P = Stop, then directly to to Q, this corresponds to law (Stop ▷ P = P)
--   if P is not Stop, then define it as ((P □ Q) ⊓ Q) .force
-- But it is problematic to distinguish them without 
force (P ▷ Q) | vis fP | _ = mix fP Q

-- force (P ▷ Q) | vis fP | ndbr fQ _ _ _ = ((P □ Q) ⊓ Q) .force

-- if P is nondeterministic choice, it distributes through ▷
-- force (P ▷ Q) | ndbr fP wi wa wp | _ = ((P □ Q) ⊓ Q) .force
force (P ▷ Q) | ndbr fP wi wa wp | _ =
  ndbr (mergeNdbr▷-L fP Q) wi wa (mergeNdbr▷-L-witness fP Q wp)

-- ▷-assoc
force (P ▷ Q) | mix fP P' | _ =
  mix fP (P' ▷ Q)
  
-------------------------------------------------------------------------------------
-- bind continuation helpers
-- These are the per-shape continuation functions used inside `_>>=_`'s
-- `force` clauses.  They are factored out of anonymous lambdas so
-- downstream proofs can reduce them via `bind-cont-*-just/nothing` lemmas.

-- bind-cont-vis: P fires a visible event, then continues into k.
bind-cont-vis : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
              → (k : R → ITree E I S)
              → ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))
              → (at : AnyTypes E) → ContinueType at (Maybe (ITree E I S))
bind-cont-vis k f at a with f at a
... | nothing  = nothing
... | just t′  = just (t′ >>= k)

-- bind-cont-ndbr: P branches via ndbr, bind threads through k per branch.
bind-cont-ndbr : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
               → (k : R → ITree E I S)
               → ((ai : AnyTypes I) → ContinueType ai (Maybe (ITree E I R)))
               → (ai : AnyTypes I) → ContinueType ai (Maybe (ITree E I S))
bind-cont-ndbr k f ai a with f ai a
... | nothing  = nothing
... | just t′  = just (t′ >>= k)

-- bind-cont-ndbr-witness: lifts the non-emptiness witness through bind.
bind-cont-ndbr-witness : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                       → (k : R → ITree E I S)
                       → (f : (ai : AnyTypes I) → ContinueType ai (Maybe (ITree E I R)))
                       → ∀ {wi wa}
                       → Is-just (f wi wa)
                       → Is-just (bind-cont-ndbr k f wi wa)
bind-cont-ndbr-witness k f {wi} {wa} p with f wi wa | p
... | just _  | _  = any-just tt₀
... | nothing | ()

-- bind-cont-mix: P is mix-shaped; bind threads through k on the vis-side.
-- (Identical in body to bind-cont-vis; kept separate for clarity.)
bind-cont-mix : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
              → (k : R → ITree E I S)
              → ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))
              → (at : AnyTypes E) → ContinueType at (Maybe (ITree E I S))
bind-cont-mix k f at a with f at a
... | nothing  = nothing
... | just t′  = just (t′ >>= k)

-------------------------------------------------------------------------------------
-- bind operator
-- _>>=_ : {R S : Set} → ITree E (ExtI I) R → (R → ITree E (ExtI I) S) → ITree E (ExtI I) S
force (_>>=_ {ℓi = ℓi} {ℓr = ℓr} {ℓs = ℓs} {I = I} {R = R} {S = S} t k) with force t
... | ret r           = (k r) .force
... | sil c           = sil (c >>= k)
... | vis f           = vis (bind-cont-vis k f)
... | ndbr f wi wa wp = ndbr (bind-cont-ndbr k f) wi wa
                             (bind-cont-ndbr-witness k f wp)
... | mix fP Q        = mix (bind-cont-mix k fP) (Q >>= k)

-------------------------------------------------------------------------------------
-- bind continuation reduction lemmas
-- When the inner continuation returns `just`, the bind-cont returns
-- `just (… >>= k)`.  When it returns `nothing`, the bind-cont returns `nothing`.

bind-cont-vis-just : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                   → (k : R → ITree E I S)
                   → (f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))
                   → (at : AnyTypes E) (a : proj₁ at)
                   → ∀ {t′} → f at a ≡ just t′
                   → bind-cont-vis k f at a ≡ just (t′ >>= k)
bind-cont-vis-just k f at a {t′} eq-j with f at a
... | just _  = case eq-j of λ { refl → refl }
... | nothing = case eq-j of λ ()

bind-cont-vis-nothing : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                      → (k : R → ITree E I S)
                      → (f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))
                      → (at : AnyTypes E) (a : proj₁ at)
                      → f at a ≡ nothing
                      → bind-cont-vis k f at a ≡ nothing
bind-cont-vis-nothing k f at a eq-n with f at a
... | nothing = refl
... | just _  = case eq-n of λ ()

bind-cont-ndbr-just : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                    → (k : R → ITree E I S)
                    → (f : (ai : AnyTypes I) → ContinueType ai (Maybe (ITree E I R)))
                    → (ai : AnyTypes I) (a : proj₁ ai)
                    → ∀ {t′} → f ai a ≡ just t′
                    → bind-cont-ndbr k f ai a ≡ just (t′ >>= k)
bind-cont-ndbr-just k f ai a {t′} eq-j with f ai a
... | just _  = case eq-j of λ { refl → refl }
... | nothing = case eq-j of λ ()

bind-cont-ndbr-nothing : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                       → (k : R → ITree E I S)
                       → (f : (ai : AnyTypes I) → ContinueType ai (Maybe (ITree E I R)))
                       → (ai : AnyTypes I) (a : proj₁ ai)
                       → f ai a ≡ nothing
                       → bind-cont-ndbr k f ai a ≡ nothing
bind-cont-ndbr-nothing k f ai a eq-n with f ai a
... | nothing = refl
... | just _  = case eq-n of λ ()

bind-cont-mix-just : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                   → (k : R → ITree E I S)
                   → (f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))
                   → (at : AnyTypes E) (a : proj₁ at)
                   → ∀ {t′} → f at a ≡ just t′
                   → bind-cont-mix k f at a ≡ just (t′ >>= k)
bind-cont-mix-just k f at a {t′} eq-j with f at a
... | just _  = case eq-j of λ { refl → refl }
... | nothing = case eq-j of λ ()

bind-cont-mix-nothing : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                      → (k : R → ITree E I S)
                      → (f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))
                      → (at : AnyTypes E) (a : proj₁ at)
                      → f at a ≡ nothing
                      → bind-cont-mix k f at a ≡ nothing
bind-cont-mix-nothing k f at a eq-n with f at a
... | nothing = refl
... | just _  = case eq-n of λ ()

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

-- Named continuation factorisations for iter-bind (mirror bind-cont-* for
-- the bind operator).  Defined between iter-bind's signature and its
-- definition so the force clauses below can reduce in terms of them, and
-- so downstream proofs (Iterate.agda's lift-iter-bind-bigstep) can use the
-- named forms in force-equality lemmas.

iter-bind-cont-vis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                   → (k : A → ITree E (ExtI I) (A ⊎ R))
                   → ((at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R))))
                   → (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))
iter-bind-cont-vis k f at a = case f at a of λ where
  nothing   → nothing
  (just t') → just (iter-bind t' k)

iter-bind-cont-ndbr : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                    → (k : A → ITree E (ExtI I) (A ⊎ R))
                    → ((ai : AnyTypes (ExtI I)) → ContinueType ai (Maybe (ITree E (ExtI I) (A ⊎ R))))
                    → (ai : AnyTypes (ExtI I)) → ContinueType ai (Maybe (ITree E (ExtI I) R))
iter-bind-cont-ndbr k f ai a = case f ai a of λ where
  nothing   → nothing
  (just t') → just (iter-bind t' k)

iter-bind-cont-ndbr-witness : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                            → (k : A → ITree E (ExtI I) (A ⊎ R))
                            → (f : (ai : AnyTypes (ExtI I)) → ContinueType ai (Maybe (ITree E (ExtI I) (A ⊎ R))))
                            → ∀ {wi wa}
                            → Is-just (f wi wa)
                            → Is-just (iter-bind-cont-ndbr k f wi wa)
iter-bind-cont-ndbr-witness k f {wi} {wa} p with f wi wa | p
... | just _  | _  = any-just tt₀
... | nothing | ()

iter-bind-cont-mix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                   → (k : A → ITree E (ExtI I) (A ⊎ R))
                   → ((at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R))))
                   → (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))
iter-bind-cont-mix k f at a = case f at a of λ where
  nothing   → nothing
  (just t') → just (iter-bind t' k)

force (iter-bind t k) with t .force
... | ret (inj₁ a′)   = sil (iter k a′)
... | ret (inj₂ r)    = ret r
... | sil c           = sil (iter-bind c k)
... | vis f           = vis (iter-bind-cont-vis k f)
... | ndbr f wi wa wp = ndbr (iter-bind-cont-ndbr k f) wi wa
                              (iter-bind-cont-ndbr-witness k f wp)
... | mix f Qt        = mix (iter-bind-cont-mix k f) (iter-bind Qt k)

iter body a = iter-bind (body a) body
