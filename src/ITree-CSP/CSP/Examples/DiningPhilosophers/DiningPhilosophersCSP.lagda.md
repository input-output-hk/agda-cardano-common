# Dining philosophers (CSP model): scaffold

This is the scaffold for a parameterised CSP dining-philosophers model.
For `n = suc (suc m)` philosophers and forks arranged in a ring, we set up
the event type `DP`, its decidable equality, the CSP operator instances, and
the ring arithmetic `_⊕1` / `_⊖1`.

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP where

open import Level using (lift) renaming (zero to lzero)
open import Data.Nat using (ℕ; suc; zero; _<?_)
open import Data.Nat.Properties using (n<1+n)
open import Data.Fin using (Fin; toℕ; fromℕ<; inject₁) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Fin.Properties using (any?)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit.Base using () renaming (tt to tt₀)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to any-just)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃; ∃₂; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; concatMap)
open import Data.Vec using (Vec; tabulate; toList)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_; _×-dec_; map′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open ITree

instance
  DecEq-⊤poly : DecEq (⊤ {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })

module Sys (m : ℕ) where
  n : ℕ
  n = suc (suc m)
  Phil = Fin n
  Fork = Fin n

  data DP : Set → Set where
    picks    : Phil → Fork → DP (⊤ {lzero})
    putsdown : Phil → Fork → DP (⊤ {lzero})

  DP-AnyTypes-≟ : (x y : AnyTypes DP) → Dec (x ≡ y)
  DP-AnyTypes-≟ (_ , picks i f) (_ , picks i′ f′) with i Fin.≟ i′ | f Fin.≟ f′
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ { refl → ¬p refl }
  ... | _        | no ¬q    = no λ { refl → ¬q refl }
  DP-AnyTypes-≟ (_ , putsdown i f) (_ , putsdown i′ f′) with i Fin.≟ i′ | f Fin.≟ f′
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ { refl → ¬p refl }
  ... | _        | no ¬q    = no λ { refl → ¬q refl }
  DP-AnyTypes-≟ (_ , picks _ _)    (_ , putsdown _ _) = no λ ()
  DP-AnyTypes-≟ (_ , putsdown _ _) (_ , picks _ _)    = no λ ()

  import CSP.Definitions.Operators {E = DP} as CSPOps
  open CSPOps DP-AnyTypes-≟
  import CSP.Definitions.Iterate {E = DP} as CSPIte
  open CSPIte DP-AnyTypes-≟
  import CSP.Definitions.AlphaParallel {E = DP} as CSPAPar
  open CSPAPar DP-AnyTypes-≟
  import CSP.Definitions.Hide {E = DP} as CSPHide
  open CSPHide DP-AnyTypes-≟

  _⊕1 : Fin n → Fin n
  _⊕1 i with suc (toℕ i) <? n
  ... | yes p = fromℕ< p
  ... | no  _ = fzero

  _⊖1 : Fin n → Fin n
  _⊖1 fzero    = fromℕ< (n<1+n (suc m))
  _⊖1 (fsuc i) = inject₁ i
```

Each philosopher `i` repeatedly picks up two forks (in a configurable order
given by `first`/`second`), then puts them both down again. Each fork `j` is
held by at most one of its two neighbouring philosophers at a time.

```agda
  PHIL : (first second : Phil → Fork) → Phil → ITree DP (ExtI DP) ⊥
  PHIL first second i =
    loop0 ( picks i (first i)     ⟶₀
            picks i (second i)    ⟶₀
            putsdown i (second i) ⟶₀
            putsdown i (first i)  ⟶₀ Skip )

  FORK : Fork → ITree DP (ExtI DP) ⊥
  FORK j =
    loop0 ( (picks j j      ⟶₀ putsdown j j      ⟶₀ Skip)
          □ (picks (j ⊖1) j ⟶₀ putsdown (j ⊖1) j ⟶₀ Skip) )
```

```agda
  AlphaP : Phil → Alpha
  AlphaP i (_ , picks    i′ f) = (i′ ≡ i) × ((f ≡ i) ⊎ (f ≡ i ⊕1))
  AlphaP i (_ , putsdown i′ f) = (i′ ≡ i) × ((f ≡ i) ⊎ (f ≡ i ⊕1))

  decAlphaP : (i : Phil) → Dec-Alpha (AlphaP i)
  decAlphaP i (_ , picks    i′ f) = (i′ Fin.≟ i) ×-dec ((f Fin.≟ i) ⊎-dec (f Fin.≟ (i ⊕1)))
  decAlphaP i (_ , putsdown i′ f) = (i′ Fin.≟ i) ×-dec ((f Fin.≟ i) ⊎-dec (f Fin.≟ (i ⊕1)))

  AlphaF : Fork → Alpha
  AlphaF j (_ , picks    p f) = (f ≡ j) × ((p ≡ j) ⊎ (p ≡ j ⊖1))
  AlphaF j (_ , putsdown p f) = (f ≡ j) × ((p ≡ j) ⊎ (p ≡ j ⊖1))

  decAlphaF : (j : Fork) → Dec-Alpha (AlphaF j)
  decAlphaF j (_ , picks    p f) = (f Fin.≟ j) ×-dec ((p Fin.≟ j) ⊎-dec (p Fin.≟ (j ⊖1)))
  decAlphaF j (_ , putsdown p f) = (f Fin.≟ j) ×-dec ((p Fin.≟ j) ⊎-dec (p Fin.≟ (j ⊖1)))
```

Hiding (`_∖_¿_¿_`) needs an `hdec`: for any visible continuation it must decide
whether some *hidden, enabled* event exists (and, if so, witness it). For a
general alphabet this is undecidable, but the DP alphabet is finite and concrete
— every event `picks p f` / `putsdown p f` carries the unit value type `⊤`, and
`p , f` range over `Fin n × Fin n`. So the question is a finite search over
`Phil × Fork`, decided with `any?` and discharged uniformly for any hidden set
`cs` / `dec` and any continuation `fP`.

```agda
  hdecDP : ∀ {ℓr} {R : Set ℓr}
         → (cs  : AnyTypes DP → Set)
         → (dec : (at : AnyTypes DP) → Dec (cs at))
         → (fP  : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) R)))
         → Dec (Σ[ at ∈ AnyTypes DP ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a)))
  hdecDP {R = R} cs dec fP = map′ to from decAll
    where
      is-just? : (m : Maybe (ITree DP (ExtI DP) R)) → Dec (Is-just m)
      is-just? (just _) = yes (any-just tt₀)
      is-just? nothing  = no λ ()

      -- the predicate, split by constructor, over the finite Phil × Fork grid
      Pp Pq : Fin n → Fin n → Set _
      Pp p f = cs (⊤ , picks    p f) × Is-just (fP (⊤ , picks    p f) tt)
      Pq p f = cs (⊤ , putsdown p f) × Is-just (fP (⊤ , putsdown p f) tt)

      Pp? : (p f : Fin n) → Dec (Pp p f)
      Pp? p f = dec (⊤ , picks    p f) ×-dec is-just? (fP (⊤ , picks    p f) tt)
      Pq? : (p f : Fin n) → Dec (Pq p f)
      Pq? p f = dec (⊤ , putsdown p f) ×-dec is-just? (fP (⊤ , putsdown p f) tt)

      decAll : Dec ((∃₂ λ p f → Pp p f) ⊎ (∃₂ λ p f → Pq p f))
      decAll = any? (λ p → any? (λ f → Pp? p f))
               ⊎-dec
               any? (λ p → any? (λ f → Pq? p f))

      -- a hidden, enabled event ⇔ the witnessing Σ the hiding operator wants
      to : ((∃₂ λ p f → Pp p f) ⊎ (∃₂ λ p f → Pq p f))
         → Σ[ at ∈ AnyTypes DP ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))
      to (inj₁ (p , f , csp , isj)) = (⊤ , picks    p f) , tt , csp , isj
      to (inj₂ (p , f , csp , isj)) = (⊤ , putsdown p f) , tt , csp , isj

      from : (Σ[ at ∈ AnyTypes DP ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a)))
           → ((∃₂ λ p f → Pp p f) ⊎ (∃₂ λ p f → Pq p f))
      from ((_ , picks    p f) , _ , csp , isj) = inj₁ (p , f , csp , isj)
      from ((_ , putsdown p f) , _ , csp , isj) = inj₂ (p , f , csp , isj)
```

With `hdecDP` in hand the hiding operator applies directly: e.g. hide a
philosopher's whole alphabet `AlphaP i` from any DP process.

```agda
  _∖Phil_ : ∀ {ℓr} {R : Set ℓr} {{_ : DecEq R}}
          → ITree DP (ExtI DP) R → Phil → ITree DP (ExtI DP) R
  P ∖Phil i = P ∖ AlphaP i ¿ decAlphaP i ¿ hdecDP (AlphaP i) (decAlphaP i)

  -- sanity: hide philosopher 0's events from fork 0's process
  hideFORK0 : ITree DP (ExtI DP) ⊥
  hideFORK0 = FORK fzero ∖Phil fzero
```

The whole system is the flat alphabetised parallel composition of all the
philosopher and fork processes. We build the component list with `comps`, then
take `∥list` of it. The symmetric instance has every philosopher pick up its
left fork first (deadlocks); the asymmetric instance flips philosopher `0`'s
order (deadlock-free).

```agda
  philComp : (first second : Phil → Fork) → Phil → Comp DP ⊥
  philComp first second i = comp (AlphaP i) (decAlphaP i) (PHIL first second i)

  forkComp : Fork → Comp DP ⊥
  forkComp j = comp (AlphaF j) (decAlphaF j) (FORK j)

  allPhils : List Phil
  allPhils = toList (tabulate (λ (i : Fin n) → i))

  comps : (first second : Phil → Fork) → List (Comp DP ⊥)
  comps first second = concatMap (λ i → philComp first second i ∷ forkComp i ∷ []) allPhils

  SYSTEM : (first second : Phil → Fork) → ITree DP (ExtI DP) (RetOf (comps first second))
  SYSTEM first second = ∥list (comps first second)

  symFirst symSecond : Phil → Fork
  symFirst  i = i
  symSecond i = i ⊕1

  asymFirst asymSecond : Phil → Fork
  asymFirst  i = if ⌊ i Fin.≟ fzero ⌋ then i ⊕1 else i
  asymSecond i = if ⌊ i Fin.≟ fzero ⌋ then i    else i ⊕1

  SYSTEMsym  : ITree DP (ExtI DP) (RetOf (comps symFirst  symSecond))
  SYSTEMsym  = SYSTEM symFirst  symSecond
  SYSTEMasym : ITree DP (ExtI DP) (RetOf (comps asymFirst asymSecond))
  SYSTEMasym = SYSTEM asymFirst asymSecond
```

Sanity check: instantiate the module at `m = 0` (so `n = 2`) and force both
systems to elaborate end-to-end.

```agda
private
  module Sanity where
    open Sys 0
    sanity-sym  = SYSTEMsym
    sanity-asym = SYSTEMasym
```
