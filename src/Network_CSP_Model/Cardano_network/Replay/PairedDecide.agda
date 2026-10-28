{-# OPTIONS --safe #-}

-- Exhaustive order-preserving merge search with a constructive decision result.
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe)
open import Cardano_network.Replay.Common using (Role; Direction)
module Cardano_network.Replay.PairedDecide
  (S M : Set) (messageEq : DecidableEquality M)
  (localNext : Role → S → Direction × M → Maybe S) where

open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s)
open import Data.Nat.Properties using (+-suc; ≤-refl)
open import Cardano_network.Replay.Common using (client; server)
open import Cardano_network.Replay.Paired S M messageEq localNext

-- A compatible pair consumes every input row once, in endpoint-local order.
-- Its witness records the chosen endpoint at every transition.
data Compatible (s : State) : List LocalEvent → List LocalEvent → Set where
  finished : Compatible s [] []
  takeClient : ∀ {e cs ss t} → Step s (client , e) t →
    Compatible t cs ss → Compatible s (e ∷ cs) ss
  takeServer : ∀ {e cs ss t} → Step s (server , e) t →
    Compatible t cs ss → Compatible s cs (e ∷ ss)

-- Removing a server row reduces the total remaining-row bound by one.
right-bound : ∀ (cs ss : List LocalEvent) {n} → length cs + suc (length ss) ≤ suc n →
  length cs + length ss ≤ n
right-bound cs ss {n} le with subst (_≤ suc n) (+-suc (length cs) (length ss)) le
... | s≤s pr = pr

-- Search is structurally recursive on an exact upper bound of remaining rows.
-- The bound cannot run out while input remains and is not a heuristic cutoff.
compatibleBound : ∀ n s cs ss → length cs + length ss ≤ n → Dec (Compatible s cs ss)
compatibleBound zero s [] [] le = yes finished
compatibleBound zero s (_ ∷ _) ss ()
compatibleBound zero s [] (_ ∷ _) ()
compatibleBound (suc n) s [] [] le = yes finished
compatibleBound (suc n) s (e ∷ cs) [] (s≤s le) with advance s (client , e)
... | disabled neg = no λ { (takeClient st _) → neg st }
... | enabled t st with compatibleBound n t cs [] le
...   | yes run = yes (takeClient st run)
...   | no neg = no λ { (takeClient st′ run) → reject st′ run }
  where
  -- Determinism aligns any purported successor with the searched one.
  reject : ∀ {u} → Step s (client , e) u → Compatible u cs [] → Data.Empty.⊥
  reject st′ run with unique st st′
  ... | refl = neg run
compatibleBound (suc n) s [] (e ∷ ss) (s≤s le) with advance s (server , e)
... | disabled neg = no λ { (takeServer st _) → neg st }
... | enabled t st with compatibleBound n t [] ss le
...   | yes run = yes (takeServer st run)
...   | no neg = no λ { (takeServer st′ run) → reject st′ run }
  where
  -- Determinism aligns the sole server-row branch.
  reject : ∀ {u} → Step s (server , e) u → Compatible u [] ss → Data.Empty.⊥
  reject st′ run with unique st st′
  ... | refl = neg run
compatibleBound (suc n) s (c ∷ cs) (e ∷ ss) (s≤s le) with advance s (client , c)
... | enabled t st with compatibleBound n t cs (e ∷ ss) le
...   | yes run = yes (takeClient st run)
...   | no neg with advance s (server , e)
...     | disabled bad = no λ
  { (takeClient st′ run) → rejectClient st′ run
  ; (takeServer st′ _) → bad st′ }
  where
  -- The failed client branch refutes every execution choosing that row first.
  rejectClient : ∀ {u} → Step s (client , c) u → Compatible u cs (e ∷ ss) → Data.Empty.⊥
  rejectClient st′ run with unique st st′
  ... | refl = neg run
...     | enabled u su with compatibleBound n u (c ∷ cs) ss (right-bound (c ∷ cs) ss (s≤s le))
...       | yes run = yes (takeServer su run)
...       | no negS = no λ
  { (takeClient st′ run) → rejectClient st′ run
  ; (takeServer su′ run) → rejectServer su′ run }
  where
  -- Both exhaustive branches failed, so neither possible first row works.
  rejectClient : ∀ {v} → Step s (client , c) v → Compatible v cs (e ∷ ss) → Data.Empty.⊥
  rejectClient st′ run with unique st st′
  ... | refl = neg run
  -- The server branch uses the same deterministic-successor argument.
  rejectServer : ∀ {v} → Step s (server , e) v → Compatible v (c ∷ cs) ss → Data.Empty.⊥
  rejectServer su′ run with unique su su′
  ... | refl = negS run
compatibleBound (suc n) s (c ∷ cs) (e ∷ ss) (s≤s le) | disabled badC with advance s (server , e)
... | disabled badS = no λ
  { (takeClient st _) → badC st ; (takeServer st _) → badS st }
... | enabled u su with compatibleBound n u (c ∷ cs) ss (right-bound (c ∷ cs) ss (s≤s le))
...   | yes run = yes (takeServer su run)
...   | no negS = no λ
  { (takeClient st _) → badC st ; (takeServer st run) → reject st run }
  where
  -- A disabled client leaves only the fully searched server branch.
  reject : ∀ {v} → Step s (server , e) v → Compatible v (c ∷ cs) ss → Data.Empty.⊥
  reject st run with unique su st
  ... | refl = negS run

-- Decide all possible interleavings with exactly sufficient structural fuel.
compatible? : ∀ s cs ss → Dec (Compatible s cs ss)
compatible? s cs ss = compatibleBound (length cs + length ss) s cs ss ≤-refl

-- Extract the actual merged sequence from an accepting decision witness.
merge : ∀ {s cs ss} → Compatible s cs ss → List Event
merge finished = []
merge (takeClient {e} st run) = (client , e) ∷ merge run
merge (takeServer {e} st run) = (server , e) ∷ merge run

-- Acceptance preserves the entire client sequence in its original order.
client-projection : ∀ {s cs ss} (run : Compatible s cs ss) → project client (merge run) ≡ cs
client-projection finished = refl
client-projection (takeClient st run) rewrite client-projection run = refl
client-projection (takeServer st run) = client-projection run

-- Acceptance likewise preserves every server row and its order.
server-projection : ∀ {s cs ss} (run : Compatible s cs ss) → project server (merge run) ≡ ss
server-projection finished = refl
server-projection (takeClient st run) = server-projection run
server-projection (takeServer st run) rewrite server-projection run = refl

-- The witness merge is a run of the independently defined paired machine.
merge-run : ∀ {s cs ss} (run : Compatible s cs ss) → HasTrace s (merge run)
merge-run finished = _ , done
merge-run (takeClient st run) with merge-run run
... | t , rest = t , vis st rest
merge-run (takeServer st run) with merge-run run
... | t , rest = t , vis st rest

-- Any paired run witnesses compatibility of its two endpoint projections.
run-compatible : ∀ {s es t} → s ⇒⟨ es ⟩ t →
  Compatible s (project client es) (project server es)
run-compatible done = finished
run-compatible (tau () _)
run-compatible (vis {e = client , e} st run) = takeClient st (run-compatible run)
run-compatible (vis {e = server , e} st run) = takeServer st (run-compatible run)

-- Explicit certificate: one merged trace, exact input projections, and a run.
record Witness (s : State) (cs ss : List LocalEvent) : Set where
  constructor witness
  field
    events : List Event
    clientOrder : project client events ≡ cs
    serverOrder : project server events ≡ ss
    execution : HasTrace s events

-- Every successful search constructs the specified observable certificate.
toWitness : ∀ {s cs ss} → Compatible s cs ss → Witness s cs ss
toWitness run = witness (merge run) (client-projection run) (server-projection run) (merge-run run)

-- Any compatible merged run is covered by the search's acceptance relation.
fromWitness : ∀ {s cs ss} → Witness s cs ss → Compatible s cs ss
fromWitness (witness es refl refl (_ , run)) = run-compatible run

-- A negative search result excludes every order-preserving valid merge.
witness? : ∀ s cs ss → Dec (Witness s cs ss)
witness? s cs ss with compatible? s cs ss
... | yes run = yes (toWitness run)
... | no neg = no λ w → neg (fromWitness w)

-- The searched predicate is exactly existence of a matching projected run.
correspondence : ∀ {s cs ss} → Compatible s cs ss ⇔ Witness s cs ss
correspondence = mk⇔ toWitness fromWitness
