{-# OPTIONS --guardedness #-}

-- Registry identity uniqueness is independent of per-allocation resource proofs.
module ConnectionManagement.Properties.RegistryUnique where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.OriginMonitor as Single
open Single using (Target; target; workerId; handleId)
open import ConnectionManagement.Rules.AttributedOrigin using (Action; allocate; dispatch; erase; ordinary)
import ConnectionManagement.Rules.AttributedOrigin as Attributed
open import ConnectionManagement.Rules.OriginRegistry

-- Each earlier entry differs from every later entry in BOTH identity fields.
Apart : Target → Target → Set
Apart t u = workerId t ≢ workerId u × handleId t ≢ handleId u
Unique : List Entry → Set
Unique es = AllPairs Apart (map targetId es)

-- The executable absence checks provide the pairwise freshness evidence.
fresh : ∀ w hid es → hasWorker w es ≡ false → hasHandle hid es ≡ false →
  All (Apart (target w hid)) (map targetId es)
fresh w hid [] fw fh = []
fresh w hid (e ∷ es) fw fh with w ≟ workerId (targetId e) | hid ≟ handleId (targetId e)
... | yes _ | _ = case fw of λ ()
... | no _ | yes _ = case fh of λ ()
... | no nw | no nh = (nw , nh) ∷ fresh w hid es fw fh

prepare-unique : ∀ a es {ready} → prepare a es ≡ just ready → Unique es → Unique ready
prepare-unique (allocate w hid mid k ps f) es eq unique
  with hasWorker w es in fw | hasHandle hid es in fh
... | true | _ = case eq of λ ()
... | false | true = case eq of λ ()
... | false | false with just-injective eq
...   | refl = fresh w hid es fw fh ∷ unique
prepare-unique (dispatch a) es eq unique with ordinary a | requiredWorker a
... | false | _ = case eq of λ ()
... | true | nothing with just-injective eq
...   | refl = unique
prepare-unique (dispatch a) es eq unique | true | just w with hasWorker w es
... | false = case eq of λ ()
... | true with just-injective eq
...   | refl = unique

-- Phase updates preserve the complete target list, including its order.
drive-targets : ∀ a c es {es′} → drive a c es ≡ just es′ → map targetId es ≡ map targetId es′
drive-targets a c [] eq with just-injective eq
... | refl = refl
drive-targets a c (e ∷ es) eq with Attributed.step (targetId e) a (Single.observed c (phase e))
... | nothing = case eq of λ ()
... | just s with drive a c es in driven
...   | nothing = case eq of λ ()
...   | just rest with just-injective eq
...     | refl = cong (targetId e ∷_) (drive-targets a c es driven)

step-unique : ∀ a s {s′} → step a s ≡ just s′ → Unique (entries s) → Unique (entries s′)
step-unique a (registry c es) eq unique with prepare a es in prepared
... | nothing = case eq of λ ()
... | just ready with Open.advance (erase a) c
...   | nothing = case eq of λ ()
...   | just c′ with drive a c ready in driven
...     | nothing = case eq of λ ()
...     | just es′ with just-injective eq
...       | refl = subst (AllPairs Apart) (drive-targets a c ready driven) (prepare-unique a es prepared unique)

exec-unique : ∀ {s as s′} → Executes s as s′ → Unique (entries s) → Unique (entries s′)
exec-unique done unique = unique
exec-unique (next {s = s} {a = a} eq path) unique = exec-unique path (step-unique a s eq unique)

-- No Supported/resource premise is needed for identity uniqueness.
reachable-unique : ∀ {c as s′} → Executes (start c) as s′ → Unique (entries s′)
reachable-unique path = exec-unique path []
