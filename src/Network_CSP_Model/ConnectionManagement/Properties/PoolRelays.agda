{-# OPTIONS --guardedness #-}

-- The outer withAsync returns only after the inner callback has returned and,
-- on a scheduled node, after its pool relays thread has been joined. A plain
-- node never gains a relays thread and a scheduled node never loses it. No
-- progress or fairness is claimed: these are finite-execution certificates.
module ConnectionManagement.Properties.PoolRelays where

open import Data.Bool using (Bool; true; false)
import Data.List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import ConnectionManagement.Rules.PoolRelays

-- Leaving `inside` needs the inner return; `finished` needs the join, if any.
Inv : Bool → State → Set
Inv ret (relaysState t inside) = ⊤
Inv ret (relaysState t cancelling) = ret ≡ true
Inv ret (relaysState nothing finished) = ret ≡ true
Inv ret (relaysState (just joined) finished) = ret ≡ true
Inv ret (relaysState (just _) finished) = ⊥

preserve : ∀ ret a r {r′} → Inv ret r → step ret a r ≡ just r′ → Inv ret r′
preserve ret a (relaysState t finished) i ()
preserve ret (threadAct a) (relaysState nothing inside) i ()
preserve ret (threadAct a) (relaysState nothing cancelling) i ()
preserve ret (threadAct a) (relaysState (just p) inside) i eq with move a inside p
... | just _ with eq
...   | refl = tt
preserve ret (threadAct a) (relaysState (just p) inside) i eq | nothing with eq
... | ()
preserve ret (threadAct a) (relaysState (just p) cancelling) i eq with move a cancelling p
... | just _ with eq
...   | refl = i
preserve ret (threadAct a) (relaysState (just p) cancelling) i eq | nothing with eq
... | ()
preserve true requestCancel (relaysState (just p) inside) i refl = refl
preserve true requestCancel (relaysState nothing inside) i ()
preserve false requestCancel (relaysState t inside) i ()
preserve ret requestCancel (relaysState t cancelling) i ()
preserve true finish (relaysState nothing inside) i refl = refl
preserve false finish (relaysState nothing inside) i ()
preserve true finish (relaysState (just p) inside) i ()
preserve false finish (relaysState (just p) inside) i ()
preserve ret finish (relaysState (just joined) cancelling) i refl = i
preserve ret finish (relaysState (just running) cancelling) i ()
preserve ret finish (relaysState (just cancelRequested) cancelling) i ()
preserve ret finish (relaysState (just cancelDelivered) cancelling) i ()
preserve ret finish (relaysState (just bodyUnwinding) cancelling) i ()
preserve ret finish (relaysState (just bodyExited) cancelling) i ()
preserve ret finish (relaysState (just resultAvailable) cancelling) i ()
preserve ret finish (relaysState nothing cancelling) i ()

-- Whether a relays thread was forked never changes.
present : State → Bool
present (relaysState (just _) o) = true
present (relaysState nothing o) = false

present-step : ∀ ret a r {r′} → step ret a r ≡ just r′ → present r′ ≡ present r
present-step ret a (relaysState t finished) ()
present-step ret (threadAct a) (relaysState nothing inside) ()
present-step ret (threadAct a) (relaysState nothing cancelling) ()
present-step ret (threadAct a) (relaysState (just p) inside) eq with move a inside p
... | just _ with eq
...   | refl = refl
present-step ret (threadAct a) (relaysState (just p) inside) eq | nothing with eq
... | ()
present-step ret (threadAct a) (relaysState (just p) cancelling) eq with move a cancelling p
... | just _ with eq
...   | refl = refl
present-step ret (threadAct a) (relaysState (just p) cancelling) eq | nothing with eq
... | ()
present-step true requestCancel (relaysState (just p) inside) refl = refl
present-step true requestCancel (relaysState nothing inside) ()
present-step false requestCancel (relaysState t inside) ()
present-step ret requestCancel (relaysState t cancelling) ()
present-step true finish (relaysState nothing inside) refl = refl
present-step false finish (relaysState nothing inside) ()
present-step true finish (relaysState (just p) inside) ()
present-step false finish (relaysState (just p) inside) ()
present-step ret finish (relaysState (just joined) cancelling) refl = refl
present-step ret finish (relaysState (just running) cancelling) ()
present-step ret finish (relaysState (just cancelRequested) cancelling) ()
present-step ret finish (relaysState (just cancelDelivered) cancelling) ()
present-step ret finish (relaysState (just bodyUnwinding) cancelling) ()
present-step ret finish (relaysState (just bodyExited) cancelling) ()
present-step ret finish (relaysState (just resultAvailable) cancelling) ()
present-step ret finish (relaysState nothing cancelling) ()

-- A running relays thread cannot return normally: its body is m Void.
running-cannot-exit : ∀ ret o → step ret (threadAct bodyExit) (relaysState (just running) o) ≡ nothing
running-cannot-exit ret inside = refl
running-cannot-exit ret cancelling = refl
running-cannot-exit ret finished = refl

module Certified {Inner InnerAction : Set}
  (innerStep : InnerAction → Inner → Maybe Inner) (returned : Inner → Bool) where
  open Outer innerStep returned

  Valid : Outer → Set
  Valid (outer i r) = Inv (returned i) r

  initial-valid : ∀ i b → Valid (outer i (initial b))
  initial-valid i true = tt
  initial-valid i false = tt

  outer-preserve : ∀ a s {s′} → Valid s → outerStep a s ≡ just s′ → Valid s′
  outer-preserve (innerAct a) (outer i (relaysState t inside)) v eq with innerStep a i
  ... | just _ with eq
  ...   | refl = tt
  outer-preserve (innerAct a) (outer i (relaysState t inside)) v eq | nothing with eq
  ... | ()
  outer-preserve (innerAct a) (outer i (relaysState t cancelling)) v ()
  outer-preserve (innerAct a) (outer i (relaysState t finished)) v ()
  outer-preserve (relaysAct a) (outer i r) v eq with step (returned i) a r in moved
  ... | just _ with eq
  ...   | refl = preserve (returned i) a r v moved
  outer-preserve (relaysAct a) (outer i r) v eq | nothing with eq
  ... | ()

  exec-preserves : ∀ {s as s′} → Executes s as s′ → Valid s → Valid s′
  exec-preserves done v = v
  exec-preserves (next {s = s} {a = a} eq path) v = exec-preserves path (outer-preserve a s v eq)

  present-one : ∀ a s {s′} → outerStep a s ≡ just s′ → present (relays s′) ≡ present (relays s)
  present-one (innerAct a) (outer i (relaysState t inside)) eq with innerStep a i
  ... | just _ with eq
  ...   | refl = refl
  present-one (innerAct a) (outer i (relaysState t inside)) eq | nothing with eq
  ... | ()
  present-one (innerAct a) (outer i (relaysState t cancelling)) ()
  present-one (innerAct a) (outer i (relaysState t finished)) ()
  present-one (relaysAct a) (outer i r) eq with step (returned i) a r in moved
  ... | just _ with eq
  ...   | refl = present-step (returned i) a r moved
  present-one (relaysAct a) (outer i r) eq | nothing with eq
  ... | ()

  present-preserved : ∀ {s as s′} → Executes s as s′ → present (relays s′) ≡ present (relays s)
  present-preserved done = refl
  present-preserved (next {s = s} {a = a} eq path) = trans (present-preserved path) (present-one a s eq)

  -- Inner steps lift while the owner is inside; relays steps lift on the
  -- inner return. Both are for composing initialized runs.
  lift-inner : ∀ a i {i′} t → innerStep a i ≡ just i′ →
    outerStep (innerAct a) (outer i (relaysState t inside)) ≡ just (outer i′ (relaysState t inside))
  lift-inner a i t eq rewrite eq = refl
  lift-relays : ∀ a i r {r′} → returned i ≡ true → step true a r ≡ just r′ →
    outerStep (relaysAct a) (outer i r) ≡ just (outer i r′)
  lift-relays a i r ret eq rewrite ret | eq = refl
  append : ∀ {s as t bs u} → Executes s as t → Executes t bs u → Executes s (as Data.List.++ bs) u
  append done rest = rest
  append (next eq path) rest = next eq (append path rest)

  -- The outer scope's return certifies the inner return and the relays join.
  finished-certifies : ∀ i t → Valid (outer i (relaysState t finished)) →
    returned i ≡ true × (t ≡ nothing ⊎ t ≡ just joined)
  finished-certifies i nothing v = v , inj₁ refl
  finished-certifies i (just joined) v = v , inj₂ refl
  finished-certifies i (just running) ()
  finished-certifies i (just cancelRequested) ()
  finished-certifies i (just cancelDelivered) ()
  finished-certifies i (just bodyUnwinding) ()
  finished-certifies i (just bodyExited) ()
  finished-certifies i (just resultAvailable) ()

  from-initial : ∀ i b {i′ t as} → Executes (outer i (initial b)) as (outer i′ (relaysState t finished)) →
    returned i′ ≡ true × (t ≡ nothing ⊎ t ≡ just joined)
  from-initial i b path = finished-certifies _ _ (exec-preserves path (initial-valid i b))
