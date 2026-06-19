# Dining philosophers (CSP model, INDEPENDENT SYSTEM' style): scaffold

This is an independent CSP dining-philosophers model. For `n = suc (suc m)`
philosophers and forks arranged in a ring, we set up the event type `DP`, its
decidable equality, the CSP operator instances (using plain `Parallel`,
without alphabets), and the ring arithmetic `_⊕1` / `_⊖1`.

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP where

open import Level using (lift) renaming (zero to lzero)
open import Data.Nat using (ℕ; suc; zero; _<?_)
open import Data.Nat.Properties using (n<1+n)
open import Data.Fin using (Fin; toℕ; fromℕ<; inject₁) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; map)
open import Data.Vec using (Vec; tabulate; toList)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Process_Trees
open PTree

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

  import CSP.Operators {E = DP} as CSPOps
  open CSPOps DP-AnyTypes-≟

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
  PHIL : (first second : Phil → Fork) → Phil → PTree DP (ExtI DP) ⊥
  PHIL first second i =
    loop0 ( picks i (first i) ⟶₀ (picks i (second i) ⟶₀
            (putsdown i (second i) ⟶₀ (putsdown i (first i) ⟶₀ Skip))) )

  FORK : Fork → PTree DP (ExtI DP) ⊥
  FORK j =
    loop0 ( (picks j j      ⟶₀ (putsdown j j      ⟶₀ Skip))
          □ (picks (j ⊖1) j ⟶₀ (putsdown (j ⊖1) j ⟶₀ Skip)) )
```

The replicated interleave `⦀list` folds the library interleave `_⦀_` over a
list of processes, with `Skip` as the unit. Its return type `IProd ps` records
the (empty) product of the component return types.

```agda
  IProd : List (PTree DP (ExtI DP) ⊥) → Set
  IProd []       = ⊤ {lzero}
  IProd (_ ∷ ps) = ⊥ × IProd ps

  ∅sync : AnyTypes DP → Set
  ∅sync _ = ⊥
  ∅sync-dec : (at : AnyTypes DP) → Dec (∅sync at)
  ∅sync-dec _ = no λ ()

  ⦀list : (ps : List (PTree DP (ExtI DP) ⊥)) → PTree DP (ExtI DP) (IProd ps)
  ⦀list []       = Skip
  ⦀list (p ∷ ps) = Par (chanSet ∅sync ∅sync-dec) _,_ p (⦀list ps)
```

`PHILS` interleaves all `n` philosophers; `FORKS` interleaves all `n` forks.
`SYSTEM′` composes them with the generalised parallel `Par`, synchronising
on the full event set (`syncAll`). Two configurations are provided: the
symmetric one (every philosopher takes the same-handed fork first, which
deadlocks) and the asymmetric one (philosopher `0` reverses its order, which is
deadlock-free).

```agda
  allPhils : List Phil
  allPhils = toList (tabulate (λ (i : Fin n) → i))

  PHILS : (first second : Phil → Fork)
        → PTree DP (ExtI DP) (IProd (map (PHIL first second) allPhils))
  PHILS first second = ⦀list (map (PHIL first second) allPhils)

  FORKS : PTree DP (ExtI DP) (IProd (map FORK allPhils))
  FORKS = ⦀list (map FORK allPhils)

  syncAll : AnyTypes DP → Set
  syncAll _ = ⊤ {lzero}
  syncAll-dec : (at : AnyTypes DP) → Dec (syncAll at)
  syncAll-dec _ = yes tt

  SYSTEM′ : (first second : Phil → Fork)
          → PTree DP (ExtI DP) (IProd (map (PHIL first second) allPhils) × IProd (map FORK allPhils))
  SYSTEM′ first second = Par (chanSet syncAll syncAll-dec) _,_ (PHILS first second) FORKS

  symFirst symSecond : Phil → Fork
  symFirst  i = i
  symSecond i = i ⊕1

  asymFirst asymSecond : Phil → Fork
  asymFirst  i = if ⌊ i Fin.≟ fzero ⌋ then i ⊕1 else i
  asymSecond i = if ⌊ i Fin.≟ fzero ⌋ then i    else i ⊕1

  SYSTEM′sym  = SYSTEM′ symFirst  symSecond
  SYSTEM′asym = SYSTEM′ asymFirst asymSecond
```

A top-level sanity check instantiates the module at `m = 0` (so `n = 2`),
forcing both the symmetric and asymmetric systems to fully elaborate.

```agda
private
  module Sanity where
    open Sys 0
    sanity-sym  = SYSTEM′sym
    sanity-asym = SYSTEM′asym
```
