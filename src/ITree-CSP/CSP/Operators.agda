{-# OPTIONS --guardedness #-}

-- SPIKE: CSP basic processes + core operators defined over the unified, witness-free
-- `react` node ONLY (no vis / ndbr / mix).  Demonstrates the simplification:
--   * every pure-visible process is `react · ∅`;
--   * `⊓` drops its index + witness entirely;
--   * `□` collapses the 9-way vis/ndbr/mix dispatch to ONE `react` clause (via a
--     (visible , τ) view), keeping only the genuinely-special `ret`/√ cases;
--   * `mix` disappears — `▷` builds `react` directly;
--   * `>>=` loses its ndbr-witness plumbing.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
open import Semantics.LTS

module CSP.Operators {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

-- NOTE: these view/continuation helpers are exposed (not `private`) so the trace
-- laws can name them in force-equation lemmas (cf. the original `mergeNdbr-*`).
module _ where
  -- the empty visible / empty τ continuations
  ∅v : ∀ {ℓr} {R : Set ℓr}
     → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
  ∅v _ _ = nothing

  ∅t : ∀ {ℓr} {R : Set ℓr}
     → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  ∅t _ _ = nothing

  -- a single τ-branch to t (lets `sil` be viewed uniformly as (∅ , oneτ))
  oneτ : ∀ {ℓr} {R : Set ℓr}
       → PTree E (ExtI E) R
       → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  oneτ t (_ , base _)   _            = nothing
  oneτ t (_ , pair _ _) _            = nothing
  oneτ t (_ , fin)      (lift fzero) = just t
  oneτ t (_ , fin)      _            = nothing

  -- read any node's visible-offer part and τ-branch part (ret/sil have no offers;
  -- sil's τ is a single branch).  Used so external choice / parallel preserve the
  -- OTHER operand's offers while one side does a τ (no divergence-starvation).
  viewV : ∀ {ℓr} {R : Set ℓr} → NodeKind E (ExtI E) R
        → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
  viewV (react v _) = v
  viewV _          = ∅v
  viewT : ∀ {ℓr} {R : Set ℓr} → NodeKind E (ExtI E) R
        → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  viewT (sil t)     = oneτ t
  viewT (react _ τc) = τc
  viewT _           = ∅t

-------------------------------------------------------------------------------------
-- Decidable event-set: a value-level (event-level) predicate with its decision.
-- Channel-level sets are the special case where `mem at a` ignores `a` (see chanSet).
-------------------------------------------------------------------------------------
record EventSet : Set (lsuc ℓ ⊔ ℓe) where
  field
    mem : (at : AnyTypes E) → proj₁ at → Set
    dec : (at : AnyTypes E) (a : proj₁ at) → Dec (mem at a)
open EventSet

chanSet : (cs : AnyTypes E → Set) → ((at : AnyTypes E) → Dec (cs at)) → EventSet
chanSet cs d .mem at _ = cs at
chanSet cs d .dec at _ = d at

∅ES : EventSet
∅ES .mem at a = ⊥
∅ES .dec at a = no (λ z → z)

-- NOTE: every operator below matches `react v τc` directly and inlines its τ-branch
-- index handling (the `pair`+`fin` tag) with recursive calls placed syntactically
-- under `just`/`sil`/`react`.  That is what lets Agda see them as productive, so all
-- of them — including hiding and parallel — typecheck WITHOUT `NON_TERMINATING`
-- (only `loop` keeps it, as `loop Skip` genuinely diverges).

-------------------------------------------------------------------------------------
-- Basic processes
-------------------------------------------------------------------------------------

Stop : ∀ {ℓr} {R : Set ℓr} → PTree E (ExtI E) R
force Stop = react ∅v ∅t                       -- stable: no offers, no τ

Ret : ∀ {ℓr} {R : Set ℓr} → R → PTree E (ExtI E) R
force (Ret r) = ret r

Skip : ∀ {ℓr} → PTree E (ExtI E) (⊤ {ℓr})
Skip = Ret tt

Tau : ∀ {ℓr} {R : Set ℓr} → PTree E (ExtI E) R → PTree E (ExtI E) R
force (Tau P) = sil P

Run : ∀ {ℓr} {R : Set ℓr} → PTree E (ExtI E) R
force Run = react (λ _ _ → just Run) ∅t

Run′ : ∀ {ℓr} {R : Set ℓr} → EventSet → PTree E (ExtI E) R
force (Run′ A) =
  react (λ at a → case A .dec at a of λ where (yes _) → just (Run′ A) ; (no _) → nothing) ∅t

guard : ∀ {ℓr} → Bool → PTree E (ExtI E) (⊤ {ℓr})
guard b = if b then Skip else Stop

-- Conditional choice  P ◁ b ▷ Q  =  if b then P else Q  (TPC/UCS `P <| b |> Q`).
infix 2 _◁_▷_
_◁_▷_ : ∀ {ℓr} {R : Set ℓr}
      → PTree E (ExtI E) R → Bool → PTree E (ExtI E) R → PTree E (ExtI E) R
P ◁ b ▷ Q = if b then P else Q

-------------------------------------------------------------------------------------
-- Internal choice — witness-free
-------------------------------------------------------------------------------------

_⊓_ : ∀ {ℓr} {R : Set ℓr}
    → PTree E (ExtI E) R → PTree E (ExtI E) R → PTree E (ExtI E) R
force (P ⊓ Q) = react ∅v (br2 P Q)            -- cf. original: ndbr (br2 P Q) idx wit witness-proof

-- Finite replicated (indexed) internal choice — a NON-EMPTY choice given as a head
-- process plus a tail list, folded by binary ⊓ (= Roscoe's ⨅ S for finite S).
⨅⁺ : ∀ {ℓr} {R : Set ℓr}
   → PTree E (ExtI E) R → List (PTree E (ExtI E) R) → PTree E (ExtI E) R
⨅⁺ P []       = P
⨅⁺ P (Q ∷ qs) = P ⊓ ⨅⁺ Q qs

-- Replicated internal choice over a finite, NON-EMPTY index ( ⊓ i : Fin (suc n) @ f i ).
⨅Fin : ∀ {ℓr} {R : Set ℓr}
     → (n : ℕ) → (Fin (suc n) → PTree E (ExtI E) R) → PTree E (ExtI E) R
⨅Fin zero    f = f fzero
⨅Fin (suc n) f = f fzero ⊓ ⨅Fin n (λ i → f (fsuc i))

-------------------------------------------------------------------------------------
-- Prefix — a pure-visible react
-------------------------------------------------------------------------------------

Prefix-cont : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
            → (e : E A) → (A → PTree E (ExtI E) R)
            → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
Prefix-cont {A = A} e P at x with E-≟ (A , e) at
... | yes refl = just (P x)
... | no  _    = nothing

Prefix : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
       → E A → (A → PTree E (ExtI E) R) → PTree E (ExtI E) R
force (Prefix e P) = react (Prefix-cont e P) ∅t
syntax Prefix e p = e ⟶ p

Prefix₀ : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
        → E A → PTree E (ExtI E) R → PTree E (ExtI E) R
syntax Prefix₀ e p = e ⟶₀ p
Prefix₀ e P = Prefix e (λ _ → P)

-- Output `e ! v ⟶ P`: a pure-visible react that offers the SINGLE carried value `v`
-- on the same event index `(A , e)` that `Prefix` (`e ⟶ P`) offers ALL values on.
-- Reader `c?x` and writer `c!v` thus share one index, differing only in the offer map.
Output-cont : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} ⦃ _ : DecEq A ⦄
            → (e : E A) → A → PTree E (ExtI E) R
            → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
Output-cont {A = A} e v P at x with E-≟ (A , e) at
... | no  _    = nothing
... | yes refl with x ≟ v
...   | yes _  = just P
...   | no  _  = nothing

Output : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} ⦃ _ : DecEq A ⦄
       → E A → A → PTree E (ExtI E) R → PTree E (ExtI E) R
force (Output e v P) = react (Output-cont e v P) ∅t

syntax Output e v p = e ! v ⟶ p

-- prefix-choice / generalised visible menu `?x:A → P(x)`: the stable, pure-visible
-- react node carrying an arbitrary offer map `v` (and an empty τ-part).  The menu A
-- is whatever events `v` offers, so this spans arbitrarily many channels.
pchoice : ∀ {ℓr} {R : Set ℓr}
        → ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
        → PTree E (ExtI E) R
pchoice v = ptree (react v ∅t)

-------------------------------------------------------------------------------------
-- Sliding / timeout — builds react directly (mix is gone)
-------------------------------------------------------------------------------------

-- The slide continuation is TOP-LEVEL (not where-bound) so trace laws can name it
-- and prove its force/branch equations (cf. the original `mergeNdbr-*` helpers).
--   left tag  (fzero)      = ALWAYS-available timeout to Q (even when P is silent/divergent);
--   right tag (fsuc fzero) = P's own τ-moves, each sliding on as (·▷Q).
mutual
  ▷-slide : ∀ {ℓr} {R : Set ℓr}
          → NodeKind E (ExtI E) R → PTree E (ExtI E) R
          → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  ▷-slide nP Q (_ , base _)            _ = nothing
  ▷-slide nP Q (_ , fin)               _ = nothing
  ▷-slide nP Q (_ , pair (base _) _)   _ = nothing
  ▷-slide nP Q (_ , pair (pair _ _) _) _ = nothing
  ▷-slide nP Q (_ , pair fin i) (lift fzero        , a) = just Q
  ▷-slide nP Q (_ , pair fin i) (lift (fsuc fzero) , a) with viewT nP (_ , i) a
  ... | just P' = just (P' ▷ Q)
  ... | nothing = nothing
  ▷-slide nP Q (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = nothing

  _▷_ : ∀ {ℓr} {R : Set ℓr}
      → PTree E (ExtI E) R → PTree E (ExtI E) R → PTree E (ExtI E) R
  force (P ▷ Q) with PTree.force P
  ... | ret r = ret r                           -- R3
  ... | nP    = react (viewV nP) (▷-slide nP Q)   -- handle sil & react uniformly (sil = (∅,oneτ))

-------------------------------------------------------------------------------------
-- External choice — ONE react clause for the non-terminating case
-------------------------------------------------------------------------------------

mergeMaybe : ∀ {ℓr} {R : Set ℓr}
           → Maybe (PTree E (ExtI E) R) → Maybe (PTree E (ExtI E) R)
           → Maybe (PTree E (ExtI E) R)
mergeMaybe nothing  nothing  = nothing
mergeMaybe (just p) nothing  = just p
mergeMaybe nothing  (just q) = just q
mergeMaybe (just p) (just q) = just (p ⊓ q)

mergeVis : ∀ {ℓr} {R : Set ℓr}
         → (vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
mergeVis vP vQ at a = mergeMaybe (vP at a) (vQ at a)

-- TOP-LEVEL slide/merge continuations (so trace laws can name them, cf. ▷-slide).
--
-- One side terminated (ret r): the live operand's visible offers pass through (via
-- `viewV`); the τ-part keeps tag0 = a τ to the TERMINATED operand (so its √ stays
-- reachable — no √-starvation), tag1 = the live operand's own τ, sliding on as (·▷·).
□-slide-RQ : ∀ {ℓr} {R : Set ℓr}            -- P terminated, Q live (Q's node = nQ)
           → PTree E (ExtI E) R → NodeKind E (ExtI E) R
           → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
□-slide-RQ P nQ (_ , base _)            _ = nothing
□-slide-RQ P nQ (_ , fin)               _ = nothing
□-slide-RQ P nQ (_ , pair (base _) _)   _ = nothing
□-slide-RQ P nQ (_ , pair (pair _ _) _) _ = nothing
□-slide-RQ P nQ (_ , pair fin i) (lift fzero , a)        = just P
□-slide-RQ P nQ (_ , pair fin i) (lift (fsuc fzero) , a) with viewT nQ (_ , i) a
... | just Q' = just (Q' ▷ P)
... | nothing = nothing
□-slide-RQ P nQ (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = nothing

□-slide-PR : ∀ {ℓr} {R : Set ℓr}            -- P live (P's node = nP), Q terminated
           → NodeKind E (ExtI E) R → PTree E (ExtI E) R
           → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
□-slide-PR nP Q (_ , base _)            _ = nothing
□-slide-PR nP Q (_ , fin)               _ = nothing
□-slide-PR nP Q (_ , pair (base _) _)   _ = nothing
□-slide-PR nP Q (_ , pair (pair _ _) _) _ = nothing
□-slide-PR nP Q (_ , pair fin i) (lift fzero , a)        = just Q
□-slide-PR nP Q (_ , pair fin i) (lift (fsuc fzero) , a) with viewT nP (_ , i) a
... | just P' = just (P' ▷ Q)
... | nothing = nothing
□-slide-PR nP Q (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = nothing

-- Fully named so every corecursive call sits under just/sil/react (no .force
-- delegation, no sumτc/mapMaybe indirection) ⇒ passes productivity, no pragma.
mutual
  -- neither side terminated: τ = P's moves (tag0 → P′□Q) ⊕ Q's moves (tag1 → P□Q′);
  -- `sil` is viewed as (∅ , oneτ), so a silent side still merges.
  □-mt : ∀ {ℓr} {R : Set ℓr} → {{ DecEq R }}
       → NodeKind E (ExtI E) R → NodeKind E (ExtI E) R
       → PTree E (ExtI E) R → PTree E (ExtI E) R
       → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  □-mt nP nQ P Q (_ , base _)            _ = nothing
  □-mt nP nQ P Q (_ , fin)               _ = nothing
  □-mt nP nQ P Q (_ , pair (base _) _)   _ = nothing
  □-mt nP nQ P Q (_ , pair (pair _ _) _) _ = nothing
  □-mt nP nQ P Q (_ , pair fin i) (lift fzero , a)        with viewT nP (_ , i) a
  ... | just P' = just (P' □ Q)
  ... | nothing = nothing
  □-mt nP nQ P Q (_ , pair fin i) (lift (fsuc fzero) , a) with viewT nQ (_ , i) a
  ... | just Q' = just (P □ Q')
  ... | nothing = nothing
  □-mt nP nQ P Q (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = nothing

  _□_ : ∀ {ℓr} {R : Set ℓr} → {{ DecEq R }}
      → PTree E (ExtI E) R → PTree E (ExtI E) R → PTree E (ExtI E) R
  force (P □ Q) with PTree.force P | PTree.force Q
  -- both terminate (√-aware)
  ... | ret r | ret r' with r ≟ r'
  ...   | yes refl = ret r
  ...   | no  _    = react ∅v (br2 P Q)                       -- = (P ⊓ Q).force, inlined
  -- P done ⇒ keep P's √ reachable (tag0 → P) while Q proceeds (uniform sil/react)
  force (P □ Q) | ret r | sil Q'      = react ∅v (□-slide-RQ P (sil Q'))
  force (P □ Q) | ret r | react vQ τcQ = react vQ (□-slide-RQ P (react vQ τcQ))
  -- Q done ⇒ keep Q's √ reachable (tag0 → Q) while P proceeds
  force (P □ Q) | sil P'      | ret r = react ∅v (□-slide-PR (sil P') Q)
  force (P □ Q) | react vP τcP | ret r = react vP (□-slide-PR (react vP τcP) Q)
  -- neither side terminated: merge offers with BOTH preserved (no starvation)
  force (P □ Q) | nP | nQ = react (mergeVis (viewV nP) (viewV nQ)) (□-mt nP nQ P Q)

-- Replicated external choice ( □ x ∈ … @ P x ).  Stop is the unit of □, so the
-- empty choice is Stop.
□⋆ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ → List (PTree E (ExtI E) R) → PTree E (ExtI E) R
□⋆ []       = Stop
□⋆ (P ∷ Ps) = P □ □⋆ Ps

□Fin : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
     → (n : ℕ) → (Fin n → PTree E (ExtI E) R) → PTree E (ExtI E) R
□Fin zero    f = Stop
□Fin (suc n) f = f fzero □ □Fin n (λ i → f (fsuc i))

-------------------------------------------------------------------------------------
-- Sequential composition / bind — ndbr-witness plumbing gone
-------------------------------------------------------------------------------------

-- TOP-LEVEL bind continuations (so >>= trace laws can name them, cf □/▷/Par/∖).
mutual
  bindV : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (k : R → PTree E (ExtI E) S)
        → NodeKind E (ExtI E) R → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) S))
  bindV k nP at a with viewV nP at a
  ... | just t  = just (t >>= k)
  ... | nothing = nothing

  bindT : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (k : R → PTree E (ExtI E) S)
        → NodeKind E (ExtI E) R → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) S))
  bindT k nP i a with viewT nP i a
  ... | just t  = just (t >>= k)
  ... | nothing = nothing

  _>>=_ : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        → PTree E (ExtI E) R → (R → PTree E (ExtI E) S) → PTree E (ExtI E) S
  force (P >>= k) with PTree.force P
  ... | ret r     = PTree.force (k r)
  ... | sil c     = sil (c >>= k)
  ... | react v τc = react (bindV k (react v τc)) (bindT k (react v τc))

_>>_ : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
     → PTree E (ExtI E) R → PTree E (ExtI E) S → PTree E (ExtI E) S
P >> Q = P >>= (λ _ → Q)

-- guarded process  b ＆ P : the guard, then P  (matches CSP.Definitions.Operators)
_＆_ : ∀ {ℓr} {R : Set ℓr} → Bool → PTree E (ExtI E) R → PTree E (ExtI E) R
b ＆ P = guard {ℓr = lzero} b >> P

-- Kleisli composition  (matches CSP.Definitions.Operators)
_>=>_ : ∀ {ℓr ℓs ℓt} {R : Set ℓr} {S : Set ℓs} {T : Set ℓt}
      → (R → PTree E (ExtI E) S) → (S → PTree E (ExtI E) T) → (R → PTree E (ExtI E) T)
(f >=> g) x = f x >>= g
infixl 1 _>=>_

-- Replicated sequential composition ( ; chaining √-terminating processes ).
-- Skip is the unit of ;, so the empty composition is Skip.
⨾⋆ : ∀ {ℓr} → List (PTree E (ExtI E) (⊤ {ℓr})) → PTree E (ExtI E) (⊤ {ℓr})
⨾⋆ []       = Skip
⨾⋆ (P ∷ Ps) = P >> ⨾⋆ Ps

⨾Fin : ∀ {ℓr} → (n : ℕ) → (Fin n → PTree E (ExtI E) (⊤ {ℓr})) → PTree E (ExtI E) (⊤ {ℓr})
⨾Fin zero    f = Skip
⨾Fin (suc n) f = f fzero >> ⨾Fin n (λ i → f (fsuc i))

-------------------------------------------------------------------------------------
-- Throw / exception:  P ⟦ A ▷ Q  (= Roscoe P [|A|> Q).  P runs; a visible P-event in
-- A transfers control to Q (P discarded); a P-event not in A continues; P's √ ends
-- normally (no throw).  Only P's τ-space ⇒ no pair-fin tag.  No DecEq.  (_⟦_▷_ is the
-- Unicode of CSPM [|A|> ; helpers keep the Θ throw mnemonic.)
-------------------------------------------------------------------------------------
infix 4 _⟦_▷_
mutual
  Θ-vis : ∀ {ℓr} {R : Set ℓr} → EventSet → NodeKind E (ExtI E) R → PTree E (ExtI E) R
        → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
  Θ-vis A nP Q at a with viewV nP at a
  ... | nothing = nothing
  ... | just P' with A .dec at a
  ...   | yes _ = just Q
  ...   | no  _ = just (P' ⟦ A ▷ Q)

  Θ-τ : ∀ {ℓr} {R : Set ℓr} → EventSet → NodeKind E (ExtI E) R → PTree E (ExtI E) R
      → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  Θ-τ A nP Q i a with viewT nP i a
  ... | just P' = just (P' ⟦ A ▷ Q)
  ... | nothing = nothing

  _⟦_▷_ : ∀ {ℓr} {R : Set ℓr}
        → PTree E (ExtI E) R → EventSet → PTree E (ExtI E) R → PTree E (ExtI E) R
  force (P ⟦ A ▷ Q) with PTree.force P
  ... | ret r = ret r
  ... | nP    = react (Θ-vis A nP Q) (Θ-τ A nP Q)

-------------------------------------------------------------------------------------
-- Interrupt:  P △ Q  (standard Roscoe).  P's events → P'△Q; Q's initial events → Q'
-- (interrupt fires, P discarded); P's τ → P'△Q; Q's τ → P△Q'; P's √ ⇒ P⊓Q
-- (nondeterministic: terminate OR let Q interrupt); an event offered by BOTH → (P'△Q) ⊓ Q'.
-- Q's √ is a terminating interrupt (reachable via the slide tag, like □'s √-preservation).  No DecEq.
-------------------------------------------------------------------------------------
infix 4 _△_
mutual
  -- asymmetric visible merge: P-offers wrapped (·△Q), Q-offers commit (interrupt fires).
  -- Takes NodeKind args directly so Agda's productivity checker sees the calls inline
  -- (same pattern as par-pVis: NodeKind → viewV inline ⇒ guarded under just/react).
  △-merge : ∀ {ℓr} {R : Set ℓr}
          → NodeKind E (ExtI E) R → NodeKind E (ExtI E) R
          → PTree E (ExtI E) R
          → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
  △-merge nP nQ Q at a with viewV nP at a | viewV nQ at a
  ... | just P' | nothing = just (P' △ Q)
  ... | nothing | just Q' = just Q'
  ... | just P' | just Q' = just (ptree (react ∅v (△-br2 P' Q Q')))
  ... | nothing | nothing = nothing

  -- τ-continuation for the both-offer ⊓ case: tag0 → P'△Q, tag1 → Q'.
  -- Defined as a named mutual helper (not br2 applied outside) so P'△Q is
  -- syntactically guarded under `just` in a mutual RHS ⇒ passes productivity.
  △-br2 : ∀ {ℓr} {R : Set ℓr}
        → PTree E (ExtI E) R → PTree E (ExtI E) R → PTree E (ExtI E) R
        → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  △-br2 P' Q Q' (_ , fin) (lift fzero)        = just (P' △ Q)
  △-br2 P' Q Q' (_ , fin) (lift (fsuc fzero)) = just Q'
  △-br2 P' Q Q' (_ , fin) _                   = nothing
  △-br2 P' Q Q' (_ , base _)   _              = nothing
  △-br2 P' Q Q' (_ , pair _ _) _              = nothing

  -- Q terminated, P live, visible merge: P-offers wrapped (·△Q); Q has no visible offers.
  △-merge-Qret : ∀ {ℓr} {R : Set ℓr}
               → NodeKind E (ExtI E) R → PTree E (ExtI E) R
               → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
  △-merge-Qret nP Q at a with viewV nP at a
  ... | just P' = just (P' △ Q)
  ... | nothing = nothing

  -- both live: tag0 = P's τ (→ P'△Q), tag1 = Q's τ (→ P△Q')  [pair-fin tag like □-mt]
  △-τ : ∀ {ℓr} {R : Set ℓr}
      → NodeKind E (ExtI E) R → NodeKind E (ExtI E) R
      → PTree E (ExtI E) R → PTree E (ExtI E) R
      → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  △-τ nP nQ P Q (_ , base _)            _ = nothing
  △-τ nP nQ P Q (_ , fin)               _ = nothing
  △-τ nP nQ P Q (_ , pair (base _) _)   _ = nothing
  △-τ nP nQ P Q (_ , pair (pair _ _) _) _ = nothing
  △-τ nP nQ P Q (_ , pair fin i) (lift fzero , a)        with viewT nP (_ , i) a
  ... | just P' = just (P' △ Q)
  ... | nothing = nothing
  △-τ nP nQ P Q (_ , pair fin i) (lift (fsuc fzero) , a) with viewT nQ (_ , i) a
  ... | just Q' = just (P △ Q')
  ... | nothing = nothing
  △-τ nP nQ P Q (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = nothing

  -- Q terminated (Q = ret r′), P live: tag0 = Q's √-interrupt (just Q, reachable via τ),
  -- tag1 = P's τ (→ P'△Q)  [mirrors □-slide-PR]
  △-slide-Qret : ∀ {ℓr} {R : Set ℓr}
               → NodeKind E (ExtI E) R → PTree E (ExtI E) R
               → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  △-slide-Qret nP Q (_ , base _)            _ = nothing
  △-slide-Qret nP Q (_ , fin)               _ = nothing
  △-slide-Qret nP Q (_ , pair (base _) _)   _ = nothing
  △-slide-Qret nP Q (_ , pair (pair _ _) _) _ = nothing
  △-slide-Qret nP Q (_ , pair fin i) (lift fzero , a)        = just Q
  △-slide-Qret nP Q (_ , pair fin i) (lift (fsuc fzero) , a) with viewT nP (_ , i) a
  ... | just P' = just (P' △ Q)
  ... | nothing = nothing
  △-slide-Qret nP Q (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = nothing

  _△_ : ∀ {ℓr} {R : Set ℓr}
      → PTree E (ExtI E) R → PTree E (ExtI E) R → PTree E (ExtI E) R
  force (P △ Q) with PTree.force P | PTree.force Q
  ... | ret r | _      = react ∅v (br2 P Q)                            -- = P ⊓ Q  (terminate OR interrupt)
  ... | nP    | ret r′ = react (△-merge-Qret nP Q) (△-slide-Qret nP Q)
  ... | nP    | nQ     = react (△-merge nP nQ Q) (△-τ nP nQ P Q)

-------------------------------------------------------------------------------------
-- Hiding — events in `cs` turn into τ.  No hdec, no witness; works for infinite cs.
-------------------------------------------------------------------------------------

-- TOP-LEVEL, tagged continuations (so trace laws can name them, cf. □/▷/Par).  The
-- τ-space is split with a `pair fin _` tag so nested hides never collide:
--   tag0 (lift fzero)        = ALL of P's own τ-moves, propagated UNCONDITIONALLY;
--   tag1 (lift (fsuc fzero)) = newly-hidden visible events (only at `base e`, e ∈ cs).
-- This is what makes hiding preserve P's τ's (Hide-τ) even under re-hiding — the old
-- scheme parked hidden events at `base e` directly, so re-hiding the same channel
-- shadowed P's nested-hide τ.  Recursion under just/react ⇒ guarded, no pragma.
mutual
  hide-hVis : ∀ {ℓr} {R : Set ℓr} (A : EventSet)
            → NodeKind E (ExtI E) R → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
  hide-hVis A nP at a with A .dec at a
  ... | yes _ = nothing
  ... | no  _ with viewV nP at a
  ...   | just P' = just (P' ∖ A)
  ...   | nothing = nothing

  -- tag1 emitter: a newly-hidden event sits at inner index `base e` (event a ∈ A);
  -- factored out so hide-hTau splits the TAG value first ⇒ reduces on an open index.
  hide-emit : ∀ {ℓr} {R : Set ℓr} (A : EventSet)
            → NodeKind E (ExtI E) R → ∀ {B} → ExtI E B → B → Maybe (PTree E (ExtI E) R)
  hide-emit A nP (base e) a with A .dec (_ , e) a
  ... | yes _ with viewV nP (_ , e) a
  ...   | just P' = just (P' ∖ A)
  ...   | nothing = nothing
  hide-emit A nP (base e) a | no _ = nothing
  hide-emit A nP (pair _ _) a = nothing
  hide-emit A nP fin       a = nothing

  hide-hTau : ∀ {ℓr} {R : Set ℓr} (A : EventSet)
            → NodeKind E (ExtI E) R → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  -- tag0: P's own τ at inner index i′, propagated (no dec — never shadowed)
  hide-hTau A nP (_ , pair fin i′) (lift fzero , a) with viewT nP (_ , i′) a
  ... | just P' = just (P' ∖ A)
  ... | nothing = nothing
  -- tag1: a newly-hidden event (only meaningful at inner index `base e`, e ∈ A)
  hide-hTau A nP (_ , pair fin i′) (lift (fsuc fzero) , a) = hide-emit A nP i′ a
  -- tags ≥ 2 and all non-`pair fin` indices: empty
  hide-hTau A nP (_ , pair fin i′) (lift (fsuc (fsuc _)) , a) = nothing
  hide-hTau A nP (_ , base _)      _ = nothing
  hide-hTau A nP (_ , fin)         _ = nothing
  hide-hTau A nP (_ , pair (base _)   _) _ = nothing
  hide-hTau A nP (_ , pair (pair _ _) _) _ = nothing

  _∖_ : ∀ {ℓr} {R : Set ℓr}
      → PTree E (ExtI E) R → EventSet → PTree E (ExtI E) R
  force (P ∖ A) with PTree.force P
  ... | ret r     = ret r
  ... | sil c     = sil (c ∖ A)
  ... | react v τc = react (hide-hVis A (react v τc)) (hide-hTau A (react v τc))

-------------------------------------------------------------------------------------
-- Parallel composition synchronising on the EventSet `A`  (and interleaving `⦀` = A = ∅)
-------------------------------------------------------------------------------------

-- GENERALISED parallel: P : PTree R₁, Q : PTree R₂, and on joint termination the two
-- return values are combined by `merge : R₁ → R₂ → R` (result PTree R).  The CSP
-- instance is R₁ = R₂ = R = ⊤ with merge = λ _ _ → tt (see `_∥_` / `_⦀_` below).
--
-- TOP-LEVEL continuations (so trace laws can name them, cf. □-mt/□-slide-*).
-- Recursive Par calls all sit under just/react/ptree ⇒ guarded, no pragma.
module _ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
         (A : EventSet) (merge : R₁ → R₂ → R) where
 mutual
  -- the both-offer interleaving overlap: (P′∥Q) ⊓ (P∥Q′)
  par-brBoth : PTree E (ExtI E) R₁ → PTree E (ExtI E) R₂          -- P  Q
             → PTree E (ExtI E) R₁ → PTree E (ExtI E) R₂          -- P′ Q′
             → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  par-brBoth P Q P' Q' (_ , fin) (lift fzero)        = just (Par P' Q)
  par-brBoth P Q P' Q' (_ , fin) (lift (fsuc fzero)) = just (Par P Q')
  par-brBoth P Q P' Q' (_ , fin) _                   = nothing
  par-brBoth P Q P' Q' (_ , base _)   _              = nothing
  par-brBoth P Q P' Q' (_ , pair _ _) _              = nothing

  -- visible: synchronise on `A`, interleave outside `A` (both-offer ⇒ inline ⊓)
  par-pVis : NodeKind E (ExtI E) R₁ → NodeKind E (ExtI E) R₂
           → PTree E (ExtI E) R₁ → PTree E (ExtI E) R₂
           → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
  par-pVis nP nQ P Q at a with A .dec at a | viewV nP at a | viewV nQ at a
  ... | yes _ | just P' | just Q' = just (Par P' Q')
  ... | yes _ | _       | _       = nothing
  ... | no  _ | just P' | just Q' = just (ptree (react (λ _ _ → nothing) (par-brBoth P Q P' Q')))
  ... | no  _ | just P' | nothing = just (Par P' Q)
  ... | no  _ | nothing | just Q' = just (Par P Q')
  ... | no  _ | nothing | nothing = nothing

  -- τ: P's moves (tag0 → P′∥Q) ⊕ Q's moves (tag1 → P∥Q′)
  par-pTau : NodeKind E (ExtI E) R₁ → NodeKind E (ExtI E) R₂
           → PTree E (ExtI E) R₁ → PTree E (ExtI E) R₂
           → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  par-pTau nP nQ P Q (_ , base _)            _ = nothing
  par-pTau nP nQ P Q (_ , fin)               _ = nothing
  par-pTau nP nQ P Q (_ , pair (base _) _)   _ = nothing
  par-pTau nP nQ P Q (_ , pair (pair _ _) _) _ = nothing
  par-pTau nP nQ P Q (_ , pair fin i) (lift fzero , a)        with viewT nP (_ , i) a
  ... | just P' = just (Par P' Q)
  ... | nothing = nothing
  par-pTau nP nQ P Q (_ , pair fin i) (lift (fsuc fzero) , a) with viewT nQ (_ , i) a
  ... | just Q' = just (Par P Q')
  ... | nothing = nothing
  par-pTau nP nQ P Q (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = nothing

  -- P terminated, Q live: Q proceeds on non-sync events / τ (sync needs absent P)
  par-hVisR : PTree E (ExtI E) R₁
            → ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₂)))
            → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
  par-hVisR P vQ at a with A .dec at a
  ... | yes _ = nothing
  ... | no  _ with vQ at a
  ...   | just Q' = just (Par P Q')
  ...   | nothing = nothing

  par-hTauR : PTree E (ExtI E) R₁
            → ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₂)))
            → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  par-hTauR P τcQ i a with τcQ i a
  ... | just Q' = just (Par P Q')
  ... | nothing = nothing

  -- Q terminated, P live: symmetric
  par-hVisL : ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₁)))
            → PTree E (ExtI E) R₂
            → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
  par-hVisL vP Q at a with A .dec at a
  ... | yes _ = nothing
  ... | no  _ with vP at a
  ...   | just P' = just (Par P' Q)
  ...   | nothing = nothing

  par-hTauL : ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₁)))
            → PTree E (ExtI E) R₂
            → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
  par-hTauL τcP Q i a with τcP i a
  ... | just P' = just (Par P' Q)
  ... | nothing = nothing

  Par : PTree E (ExtI E) R₁ → PTree E (ExtI E) R₂ → PTree E (ExtI E) R
  force (Par P Q) with PTree.force P | PTree.force Q
  ... | ret r₁ | ret r₂   = ret (merge r₁ r₂)              -- both terminate ⇒ merge values
  ... | ret r₁ | sil Q'   = sil (Par P Q')                 -- ret offers nothing ⇒ no starvation
  ... | sil P' | ret r₂   = sil (Par P' Q)
  ... | ret r₁ | react vQ τcQ = react (par-hVisR P vQ) (par-hTauR P τcQ)
  ... | react vP τcP | ret r₂ = react (par-hVisL vP Q) (par-hTauL τcP Q)
  ... | nP | nQ = react (par-pVis nP nQ P Q) (par-pTau nP nQ P Q)

-- CSP parallel instance: R₁ = R₂ = R = ⊤, merge = λ _ _ → tt (joint √ returns tt).
Par⊤ : ∀ {ℓr} → EventSet
     → PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr})
Par⊤ A P Q = Par A (λ _ _ → tt) P Q

-- Interleaving: CSP parallel with empty synchronisation set
_⦀_ : ∀ {ℓr} → PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr})
P ⦀ Q = Par ∅ES (λ _ _ → tt) P Q

-- Replicated interleaving (CSP `|||`).  Skip is the unit of `|||`, so the
-- empty interleaving is Skip; otherwise fold the list with binary `⦀`.
⦀⋆ : ∀ {ℓr} → List (PTree E (ExtI E) (⊤ {ℓr})) → PTree E (ExtI E) (⊤ {ℓr})
⦀⋆ []       = Skip
⦀⋆ (P ∷ Ps) = P ⦀ ⦀⋆ Ps

-- Replicated interleaving over a finite index:  ||| i : Fin n @ f i .
⦀Fin : ∀ {ℓr} → (n : ℕ) → (Fin n → PTree E (ExtI E) (⊤ {ℓr}))
              → PTree E (ExtI E) (⊤ {ℓr})
⦀Fin zero    f = Skip
⦀Fin (suc n) f = f fzero ⦀ ⦀Fin n (λ i → f (fsuc i))

infix 4 _∥⇘_⇙_
_∥⇘_⇙_ : ∀ {ℓr} → PTree E (ExtI E) (⊤ {ℓr}) → EventSet → PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr})
P ∥⇘ A ⇙ Q = Par⊤ A P Q

-- Replicated parallel over a NON-EMPTY index, all sharing one sync set A.
-- [|A|] has no clean unit, so this is head+list (cf. ⨅⁺), not empty-safe.
∥⁺ : ∀ {ℓr} → EventSet
   → PTree E (ExtI E) (⊤ {ℓr}) → List (PTree E (ExtI E) (⊤ {ℓr})) → PTree E (ExtI E) (⊤ {ℓr})
∥⁺ A P []       = P
∥⁺ A P (Q ∷ Qs) = P ∥⇘ A ⇙ (∥⁺ A Q Qs)

∥Fin : ∀ {ℓr} → EventSet
     → (n : ℕ) → (Fin (suc n) → PTree E (ExtI E) (⊤ {ℓr})) → PTree E (ExtI E) (⊤ {ℓr})
∥Fin A zero    f = f fzero
∥Fin A (suc n) f = f fzero ∥⇘ A ⇙ (∥Fin A n (λ i → f (fsuc i)))

-------------------------------------------------------------------------------------
-- Binary alphabetised parallel composition  P ⟦ A ∥ B ⟧ Q
--
-- Unlike the interface parallel `Par`, there is no `Fin 2` "who moves" interleave
-- branch here: alphabet membership routes every visible event determinately
-- (synchronise / P-solo / Q-solo / refuse), so no nondeterministic choice arises.
-- It is a FRESH `react` node (NOT the shared-set `Par`).
--
-- Per-component alphabets are value-level `EventSet`s (cf. `Par`): membership of a
-- visible event `(at , a)` may depend on the carried value `a`, decided by `_ .dec at a`.
--
-- GENERALISED with `merge : R₁ → R₂ → R` (mirrors `Par`): on joint termination the
-- two return values are combined by `merge`.  The product instance `merge = _,_` is the
-- public mixfix `_⟦_∥_⟧_` (see below); the named `αpar` carries an arbitrary `merge`.

infixr 5 _⟦_∥_⟧_

module _ {ℓi ℓr ℓs ℓt} {I : Set ℓ → Set ℓi} {R₁ : Set ℓr} {R₂ : Set ℓs} {R : Set ℓt}
         (A : EventSet) (B : EventSet) (merge : R₁ → R₂ → R) where
 mutual
  -- visible map: per event `(at , a)`, route by `(A .dec at a , B .dec at a)`:
  --   (yes,yes) → synchronise (both must offer `just`, else refused)
  --   (yes,no)  → P solo
  --   (no,yes)  → Q solo
  --   (no,no)   → refused
  αpar-pVis : ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R₁)))
            → ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R₂)))
            → PTree E (ExtI I) R₁ → PTree E (ExtI I) R₂
            → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))
  αpar-pVis vP vQ P Q at a with A .dec at a | B .dec at a
  ... | yes _ | yes _ with vP at a | vQ at a
  ...   | just P' | just Q' = just (αpar P' Q')
  ...   | _       | _       = nothing
  αpar-pVis vP vQ P Q at a | yes _ | no _ with vP at a
  ...   | just P' = just (αpar P' Q)
  ...   | nothing = nothing
  αpar-pVis vP vQ P Q at a | no _ | yes _ with vQ at a
  ...   | just Q' = just (αpar P Q')
  ...   | nothing = nothing
  αpar-pVis vP vQ P Q at a | no _ | no _ = nothing

  -- τ map: distribute BOTH sides' τ-branches.  Tag0 → P's τ (P′ ∥ Q),
  -- tag1 → Q's τ (P ∥ Q′).  No interleave overlap (no `par-brBoth`).
  αpar-pTau : ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R₁)))
            → ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R₂)))
            → PTree E (ExtI I) R₁ → PTree E (ExtI I) R₂
            → (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))
  αpar-pTau τcP τcQ P Q (_ , base _)            _ = nothing
  αpar-pTau τcP τcQ P Q (_ , fin)               _ = nothing
  αpar-pTau τcP τcQ P Q (_ , pair (base _) _)   _ = nothing
  αpar-pTau τcP τcQ P Q (_ , pair (pair _ _) _) _ = nothing
  αpar-pTau τcP τcQ P Q (_ , pair fin i) (lift fzero , a)        with τcP (_ , i) a
  ... | just P' = just (αpar P' Q)
  ... | nothing = nothing
  αpar-pTau τcP τcQ P Q (_ , pair fin i) (lift (fsuc fzero) , a) with τcQ (_ , i) a
  ... | just Q' = just (αpar P Q')
  ... | nothing = nothing
  αpar-pTau τcP τcQ P Q (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = nothing

  -- P terminated, Q live: Q's events routed by B alone (P contributes its return r).
  αpar-hVisR : R₁ → ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R₂)))
             → PTree E (ExtI I) R₁ → PTree E (ExtI I) R₂
             → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))
  αpar-hVisR r vQ P Q at a with A .dec at a | B .dec at a
  ... | no _ | yes _ with vQ at a
  ...   | just Q' = just (αpar P Q')
  ...   | nothing = nothing
  αpar-hVisR r vQ P Q at a | yes _ | _    = nothing
  αpar-hVisR r vQ P Q at a | no _  | no _ = nothing

  αpar-hTauR : R₁ → ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R₂)))
             → PTree E (ExtI I) R₁ → PTree E (ExtI I) R₂
             → (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))
  αpar-hTauR r τcQ P Q i a with τcQ i a
  ... | just Q' = just (αpar P Q')
  ... | nothing = nothing

  -- Q terminated, P live: symmetric (P's events routed by A alone).
  αpar-hVisL : R₂ → ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R₁)))
             → PTree E (ExtI I) R₁ → PTree E (ExtI I) R₂
             → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))
  αpar-hVisL s vP P Q at a with A .dec at a | B .dec at a
  ... | yes _ | no _ with vP at a
  ...   | just P' = just (αpar P' Q)
  ...   | nothing = nothing
  αpar-hVisL s vP P Q at a | no _  | _     = nothing
  αpar-hVisL s vP P Q at a | yes _ | yes _ = nothing

  αpar-hTauL : R₂ → ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R₁)))
             → PTree E (ExtI I) R₁ → PTree E (ExtI I) R₂
             → (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))
  αpar-hTauL s τcP P Q i a with τcP i a
  ... | just P' = just (αpar P' Q)
  ... | nothing = nothing

  αpar : PTree E (ExtI I) R₁ → PTree E (ExtI I) R₂ → PTree E (ExtI I) R
  force (αpar P Q) with PTree.force P | PTree.force Q
  ... | sil P' | _              = sil (αpar P' Q)
  ... | ret r  | sil Q'         = sil (αpar P Q')
  ... | react _ _ | sil Q'      = sil (αpar P Q')
  ... | ret r  | ret s          = ret (merge r s)
  ... | ret r  | react vQ τcQ   = react (αpar-hVisR r vQ P Q) (αpar-hTauR r τcQ P Q)
  ... | react vP τcP | ret s    = react (αpar-hVisL s vP P Q) (αpar-hTauL s τcP P Q)
  ... | react vP τcP | react vQ τcQ =
        react (αpar-pVis vP vQ P Q) (αpar-pTau τcP τcQ P Q)

-- public name: the product (`_,_`) special case, with the value-level EventSet mixfix
-- signature (cf. `Par⊤`/`_∥⇘_⇙_` as the named-`Par` instances).
_⟦_∥_⟧_ :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → PTree E (ExtI I) R
  → (A : EventSet) → (B : EventSet)
  → PTree E (ExtI I) S
  → PTree E (ExtI I) (R × S)
P ⟦ A ∥ B ⟧ Q = αpar A B _,_ P Q

-------------------------------------------------------------------------------------
-- LTS step / offer lemmas (react-headed operands)

private
  -- Force-reduction: when both operands are react-headed the composite's force is a
  -- `react` node; we return the offer function existentially (Agda infers it).
  αpar-force-react-react :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : EventSet} {B : EventSet}
      {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
      {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))}
      {τcP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))}
      {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) S))}
      {τcQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) S))}
    → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ
    → Σ-syntax ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) (R × S))))
        (λ v → Σ-syntax ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) (R × S))))
          (λ τc → (P ⟦ A ∥ B ⟧ Q) .force ≡ react v τc))
  αpar-force-react-react eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  -- Offer lemma: synchronisation case (event in both alphabets, both offer).
  αpar-sync-offer-at :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : EventSet} {B : EventSet}
      {P P′ : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
      {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))}
      {τcP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))}
      {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) S))}
      {τcQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) S))}
      {at : AnyTypes E} {a : proj₁ at}
      {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) (R × S)))}
      {τc : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) (R × S)))}
    → A .mem at a → B .mem at a
    → P .force ≡ react vP τcP → vP at a ≡ just P′
    → Q .force ≡ react vQ τcQ → vQ at a ≡ just Q′
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ react v τc
    → v at a ≡ just (P′ ⟦ A ∥ B ⟧ Q′)
  αpar-sync-offer-at {A = A} {B = B} {vP = vP} {vQ = vQ} {at = at} {a = a}
                     mA mB eqP bP eqQ bQ feq
    rewrite eqP | eqQ
    with feq
  ... | refl with A .dec at a | B .dec at a
  ...   | yes _ | yes _ with vP at a | vQ at a | bP | bQ
  ...     | just _ | just _ | refl | refl = refl
  αpar-sync-offer-at mA mB eqP bP eqQ bQ feq | refl | yes _ | no ¬B = ⊥-elim (¬B mB)
  αpar-sync-offer-at mA mB eqP bP eqQ bQ feq | refl | no ¬A | _     = ⊥-elim (¬A mA)

  -- Offer lemma: P-solo (event in A only).
  αpar-soloL-offer-at :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : EventSet} {B : EventSet}
      {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
      {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))}
      {τcP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))}
      {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) S))}
      {τcQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) S))}
      {at : AnyTypes E} {a : proj₁ at}
      {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) (R × S)))}
      {τc : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) (R × S)))}
    → A .mem at a → ¬ (B .mem at a)
    → P .force ≡ react vP τcP → vP at a ≡ just P′
    → Q .force ≡ react vQ τcQ
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ react v τc
    → v at a ≡ just (P′ ⟦ A ∥ B ⟧ Q)
  αpar-soloL-offer-at {A = A} {B = B} {vP = vP} {at = at} {a = a}
                      mA ¬mB eqP bP eqQ feq
    rewrite eqP | eqQ
    with feq
  ... | refl with A .dec at a | B .dec at a
  ...   | yes _ | no _ with vP at a | bP
  ...     | just _ | refl = refl
  αpar-soloL-offer-at mA ¬mB eqP bP eqQ feq | refl | yes _ | yes mB = ⊥-elim (¬mB mB)
  αpar-soloL-offer-at mA ¬mB eqP bP eqQ feq | refl | no ¬A | _      = ⊥-elim (¬A mA)

  -- Offer lemma: Q-solo (event in B only).
  αpar-soloR-offer-at :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : EventSet} {B : EventSet}
      {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
      {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))}
      {τcP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))}
      {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) S))}
      {τcQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) S))}
      {at : AnyTypes E} {a : proj₁ at}
      {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) (R × S)))}
      {τc : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) (R × S)))}
    → ¬ (A .mem at a) → B .mem at a
    → P .force ≡ react vP τcP
    → Q .force ≡ react vQ τcQ → vQ at a ≡ just Q′
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ react v τc
    → v at a ≡ just (P ⟦ A ∥ B ⟧ Q′)
  αpar-soloR-offer-at {A = A} {B = B} {vQ = vQ} {at = at} {a = a}
                      ¬mA mB eqP eqQ bQ feq
    rewrite eqP | eqQ
    with feq
  ... | refl with A .dec at a | B .dec at a
  ...   | no _ | yes _ with vQ at a | bQ
  ...     | just _ | refl = refl
  αpar-soloR-offer-at ¬mA mB eqP eqQ bQ feq | refl | yes mA | _     = ⊥-elim (¬mA mA)
  αpar-soloR-offer-at ¬mA mB eqP eqQ bQ feq | refl | no _   | no ¬B = ⊥-elim (¬B mB)

  -- Refusal: both react-headed and event in neither alphabet ⇒ merged offer `nothing`.
  αpar-refuse-offer-at :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : EventSet} {B : EventSet}
      {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
      {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))}
      {τcP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))}
      {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) S))}
      {τcQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) S))}
      {at : AnyTypes E} {a : proj₁ at}
      {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) (R × S)))}
      {τc : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) (R × S)))}
      {T : PTree E (ExtI I) (R × S)}
    → ¬ (A .mem at a) → ¬ (B .mem at a)
    → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ
    → (P ⟦ A ∥ B ⟧ Q) .force ≡ react v τc
    → ¬ (v at a ≡ just T)
  αpar-refuse-offer-at {A = A} {B = B} {at = at} {a = a}
                       ¬mA ¬mB eqP eqQ feq branch-eq
    rewrite eqP | eqQ with feq
  ... | refl with A .dec at a | B .dec at a
  ...   | no _   | no _   = case branch-eq of λ ()
  ...   | yes mA | _      = ⊥-elim (¬mA mA)
  ...   | no _   | yes mB = ⊥-elim (¬mB mB)

-- Public LTS step / refusal lemmas.

αpar-sync-step :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : EventSet} {B : EventSet}
    {P P′ : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
    {vP τcP vQ τcQ} {at : AnyTypes E} {a : proj₁ at}
  → A .mem at a → B .mem at a
  → P .force ≡ react vP τcP → vP at a ≡ just P′
  → Q .force ≡ react vQ τcQ → vQ at a ≡ just Q′
  → (P ⟦ A ∥ B ⟧ Q)
      ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
    (P′ ⟦ A ∥ B ⟧ Q′)
αpar-sync-step mA mB eqP bP eqQ bQ
  with αpar-force-react-react eqP eqQ
... | v , τc , feq = sVis feq (αpar-sync-offer-at mA mB eqP bP eqQ bQ feq)

αpar-soloL-step :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : EventSet} {B : EventSet}
    {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
    {vP τcP vQ τcQ} {at : AnyTypes E} {a : proj₁ at}
  → A .mem at a → ¬ (B .mem at a)
  → P .force ≡ react vP τcP → vP at a ≡ just P′
  → Q .force ≡ react vQ τcQ
  → (P ⟦ A ∥ B ⟧ Q)
      ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
    (P′ ⟦ A ∥ B ⟧ Q)
αpar-soloL-step mA ¬mB eqP bP eqQ
  with αpar-force-react-react eqP eqQ
... | v , τc , feq = sVis feq (αpar-soloL-offer-at mA ¬mB eqP bP eqQ feq)

αpar-soloR-step :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : EventSet} {B : EventSet}
    {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
    {vP τcP vQ τcQ} {at : AnyTypes E} {a : proj₁ at}
  → ¬ (A .mem at a) → B .mem at a
  → P .force ≡ react vP τcP
  → Q .force ≡ react vQ τcQ → vQ at a ≡ just Q′
  → (P ⟦ A ∥ B ⟧ Q)
      ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
    (P ⟦ A ∥ B ⟧ Q′)
αpar-soloR-step ¬mA mB eqP eqQ bQ
  with αpar-force-react-react eqP eqQ
... | v , τc , feq = sVis feq (αpar-soloR-offer-at ¬mA mB eqP eqQ bQ feq)

-- Out-of-alphabet refusal: an event in neither alphabet is refused.  Per T4 the only
-- visible step out of a react-headed composite is `sVis`; `sRet`/`sSil` are refuted by
-- the force equalities, and `sTau` carries a `τ` label so it cannot match an `ev …`.
αpar-refuse-out :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : EventSet} {B : EventSet}
    {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
    {vP τcP vQ τcQ} {at : AnyTypes E} {a : proj₁ at}
    {T : PTree E (ExtI I) (R × S)}
  → ¬ (A .mem at a) → ¬ (B .mem at a)
  → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ
  → ¬ ((P ⟦ A ∥ B ⟧ Q)
         ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► T)
αpar-refuse-out ¬mA ¬mB eqP eqQ (sVis feq branch-eq) =
  αpar-refuse-offer-at ¬mA ¬mB eqP eqQ feq branch-eq

-------------------------------------------------------------------------------------
-- Replicated (list-folded) alphabetised parallel — NON-EMPTY (head + tail list).
--
-- Convention: `⋆` = empty-safe (the operator has a unit, so the empty list is allowed,
-- e.g. `⦀⋆`/`□⋆`/`⨾⋆`); `⁺` = NON-EMPTY (no unit / head+list, e.g. `∥ₐ⁺`/`∥⁺`/`⨅⁺`).
-- Alphabetised parallel `[|A|]` has no clean unit, hence head+list here.
--
-- A finite collection of homogeneous components, each carrying its own alphabet,
-- composed by a right fold of the binary operator.  The per-layer interface is the
-- head alphabet composed with the union of the tail's alphabets (a hand-rolled `Any`).

record Comp {ℓi ℓr} (I : Set ℓ → Set ℓi) (R : Set ℓr) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr) where
  constructor comp
  field
    alpha : EventSet
    proc  : PTree E (ExtI I) R
open Comp

-- Union alphabet (a value-level `EventSet`): an event `(at , a)` is in the union when
-- it is in some component's alphabet.  `mem` is the ⊎-recursion over members; `dec` is
-- the corresponding ⊎-dec recursion.  The empty list is the empty event-set `∅ES`.
unionα : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} → List (Comp I R) → EventSet
unionα []       = ∅ES
unionα (c ∷ xs) .mem at a = Comp.alpha c .mem at a ⊎ unionα xs .mem at a
unionα (c ∷ xs) .dec at a = (Comp.alpha c .dec at a) ⊎-dec (unionα xs .dec at a)

-- Non-empty nested-product return type: one R per component (head + tail), no ⊤ base.
RetOf⁺ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} → Comp I R → List (Comp I R) → Set ℓr
RetOf⁺ {R = R} c []       = R
RetOf⁺ {R = R} c (d ∷ ds) = R × RetOf⁺ d ds

-- The fold: each head is composed (binary, product `_,_`) against the union of the tail.
∥ₐ⁺ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → (c : Comp I R) (xs : List (Comp I R)) → PTree E (ExtI I) (RetOf⁺ c xs)
∥ₐ⁺ c []       = Comp.proc c
∥ₐ⁺ c (d ∷ ds) = αpar (Comp.alpha c) (unionα (d ∷ ds)) _,_ (Comp.proc c) (∥ₐ⁺ d ds)

-- Head-layer unfolding: the cons clause is definitionally the binary composition
-- of the head against the folded tail.
∥ₐ⁺-unfold :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    (c d : Comp I R) (ds : List (Comp I R))
  → ∥ₐ⁺ c (d ∷ ds)
      ≡ αpar (Comp.alpha c) (unionα (d ∷ ds)) _,_ (Comp.proc c) (∥ₐ⁺ d ds)
∥ₐ⁺-unfold c d ds = refl

-------------------------------------------------------------------------------------
-- Iteration — productive via the sil-guarded loop-back, so NO NON_TERMINATING.
-- Mirrors CSP.Definitions.Operators.iter/iter-bind, witness-free over react.
-- `iter k a` runs `k a : PTree (A ⊎ R)`; ret (inj₁ a′) loops (guarded by sil),
-- ret (inj₂ r) terminates.
-------------------------------------------------------------------------------------

iter : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
     → (A → PTree E (ExtI E) (A ⊎ R)) → A → PTree E (ExtI E) R
iter-bind : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
          → PTree E (ExtI E) (A ⊎ R) → (A → PTree E (ExtI E) (A ⊎ R)) → PTree E (ExtI E) R
-- TOP-LEVEL iter-bind continuations (so iteration trace laws can name them, cf >>=).
iterV : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
      → (A → PTree E (ExtI E) (A ⊎ R)) → NodeKind E (ExtI E) (A ⊎ R)
      → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
iterT : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
      → (A → PTree E (ExtI E) (A ⊎ R)) → NodeKind E (ExtI E) (A ⊎ R)
      → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
force (iter-bind t k) with PTree.force t
... | ret (inj₁ a′) = sil (iter k a′)            -- loop back, guarded by sil
... | ret (inj₂ r)  = ret r                       -- done
... | sil c         = sil (iter-bind c k)
... | react v τc     = react (iterV k (react v τc)) (iterT k (react v τc))
iterV k nP at a with viewV nP at a
... | just t′ = just (iter-bind t′ k)
... | nothing = nothing
iterT k nP i a with viewT nP i a
... | just t′ = just (iter-bind t′ k)
... | nothing = nothing
iter k a = iter-bind (k a) k

-- stateful forever loop (HKTree A → KTree A R): thread the state, never return
loop : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
     → (A → PTree E (ExtI E) A) → A → PTree E (ExtI E) R
loop {A = A} {R = R} body a = iter step a
  where
    step : A → PTree E (ExtI E) (A ⊎ R)
    step a = body a >>= λ a′ → Ret (inj₁ a′)

-- non-stateful forever loop
loop0 : ∀ {ℓr} {R : Set ℓr} → PTree E (ExtI E) ⊤ → PTree E (ExtI E) R
loop0 body = loop (λ _ → body) tt

-- conditional loop (mirrors the existing loopc)
loopc : ∀ {ℓr} {R : Set ℓr} → PTree E (ExtI E) ⊤ → PTree E (ExtI E) R
loopc body = loop (λ _ → body) tt

-- while loop: iterate body while cond holds; return the final state when it fails
while : ∀ {A : Set ℓ}
      → (A → Bool) → (A → PTree E (ExtI E) A) → A → PTree E (ExtI E) A
while {A = A} cond body a = iter step a
  where
    step : A → PTree E (ExtI E) (A ⊎ A)
    step a = body a >>= λ a′ → Ret (if cond a′ then inj₁ a′ else inj₂ a′)
