{-# OPTIONS --guardedness #-}

-- Dictionary-relative text for the raw bridge labels. Tokens are zero-based
-- unary offsets: '+' skips one and ':' skips ten dictionary entries; '.' terminates an event line.
-- The dictionary retains the full typed action, including every nested payload.
open import Data.Maybe using (Maybe)
open import Data.List using (List)
module ConnectionManagement.Exploration.Text
  (State Action : Set) (advance : Action → State → Maybe State)
  (dictionary : List Action) where

open import Data.Char using (Char)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import ConnectionManagement.Exploration.Finite
import ConnectionManagement.CSP.Dispatcher as Dispatcher
module Raw = Dispatcher State Action advance

-- Print a covered bridge label; membership selects an alias when the dictionary
-- contains duplicates. The round trip recovers the LABEL, not its alias index.
printLabel : ∀ {a : Action} {xs : List Action} → a ∈ xs → List Char
printLabel here = '.' ∷ '\n' ∷ []
printLabel (there here) = '+' ∷ '.' ∷ '\n' ∷ []
printLabel (there (there here)) = '+' ∷ '+' ∷ '.' ∷ '\n' ∷ []
printLabel (there (there (there here))) = '+' ∷ '+' ∷ '+' ∷ '.' ∷ '\n' ∷ []
printLabel (there (there (there (there here)))) = '+' ∷ '+' ∷ '+' ∷ '+' ∷ '.' ∷ '\n' ∷ []
printLabel (there (there (there (there (there here))))) = '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '.' ∷ '\n' ∷ []
printLabel (there (there (there (there (there (there here)))))) = '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '.' ∷ '\n' ∷ []
printLabel (there (there (there (there (there (there (there here))))))) = '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '.' ∷ '\n' ∷ []
printLabel (there (there (there (there (there (there (there (there here)))))))) = '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '.' ∷ '\n' ∷ []
printLabel (there (there (there (there (there (there (there (there (there here))))))))) = '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '+' ∷ '.' ∷ '\n' ∷ []
printLabel (there (there (there (there (there (there (there (there (there (there p)))))))))) = ':' ∷ printLabel p

parseLabel : List Action → List Char → Maybe (Action × List Char)
parseLabel [] cs = nothing
parseLabel (a ∷ as) ('.' ∷ '\n' ∷ cs) = just (a , cs)
parseLabel (a ∷ as) ('+' ∷ cs) = parseLabel as cs
parseLabel (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ as) (':' ∷ cs) = parseLabel as cs
parseLabel _ _ = nothing

parse-print-label : ∀ {a : Action} {xs : List Action} (p : a ∈ xs) cs →
  parseLabel xs (printLabel p ++ cs) ≡ just (a , cs)
parse-print-label here cs = refl
parse-print-label (there here) cs = refl
parse-print-label (there (there here)) cs = refl
parse-print-label (there (there (there here))) cs = refl
parse-print-label (there (there (there (there here)))) cs = refl
parse-print-label (there (there (there (there (there here))))) cs = refl
parse-print-label (there (there (there (there (there (there here)))))) cs = refl
parse-print-label (there (there (there (there (there (there (there here))))))) cs = refl
parse-print-label (there (there (there (there (there (there (there (there here)))))))) cs = refl
parse-print-label (there (there (there (there (there (there (there (there (there here))))))))) cs = refl
parse-print-label (there (there (there (there (there (there (there (there (there (there p)))))))))) cs = parse-print-label p cs

-- Parsing recurses on explicit fuel (the byte count at the public boundary).
-- This also prevents a malformed or zero-consumption parser from looping.
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (length)
parse : ℕ → List Char → Maybe (List Action)
parse n [] = just []
parse zero (_ ∷ _) = nothing
parse (suc n) cs@(_ ∷ _) with parseLabel dictionary cs
... | nothing = nothing
... | just (a , rest) with parse n rest
...   | nothing = nothing
...   | just as = just (a ∷ as)

print : ∀ {as} → Covered as dictionary → List Char
print {[]} covered = []
print {a ∷ as} (p , ps) = printLabel p ++ print ps

-- More fuel than event count is harmless; bytes are always a sufficient fuel.
round-trip : ∀ {as} (covered : Covered as dictionary) →
  parse (length as) (print covered) ≡ just as
round-trip {[]} covered = refl
round-trip {a ∷ as} (here , ps) rewrite round-trip ps = refl
round-trip {a ∷ as} (p@(there here) , ps)
  rewrite parse-print-label p (print ps) | round-trip ps = refl
round-trip {a ∷ as} (p@(there (there here)) , ps)
  rewrite parse-print-label p (print ps) | round-trip ps = refl
round-trip {a ∷ as} (p@(there (there (there here))) , ps)
  rewrite parse-print-label p (print ps) | round-trip ps = refl
round-trip {a ∷ as} (p@(there (there (there (there here)))) , ps)
  rewrite parse-print-label p (print ps) | round-trip ps = refl
round-trip {a ∷ as} (p@(there (there (there (there (there here))))) , ps)
  rewrite parse-print-label p (print ps) | round-trip ps = refl
round-trip {a ∷ as} (p@(there (there (there (there (there (there here)))))) , ps)
  rewrite parse-print-label p (print ps) | round-trip ps = refl
round-trip {a ∷ as} (p@(there (there (there (there (there (there (there here))))))) , ps)
  rewrite parse-print-label p (print ps) | round-trip ps = refl
round-trip {a ∷ as} (p@(there (there (there (there (there (there (there (there here)))))))) , ps)
  rewrite parse-print-label p (print ps) | round-trip ps = refl
round-trip {a ∷ as} (p@(there (there (there (there (there (there (there (there (there here))))))))) , ps)
  rewrite parse-print-label p (print ps) | round-trip ps = refl
round-trip {a ∷ as} (p@(there (there (there (there (there (there (there (there (there (there q)))))))))) , ps)
  rewrite parse-print-label p (print ps) | round-trip ps = refl

-- The executable checker replays every parsed action using the real dispatcher.
replay : List Action → State → Maybe State
replay [] s = just s
replay (a ∷ as) s with advance a s
... | nothing = nothing
... | just t = replay as t

replay-sound : ∀ as s {t} → replay as s ≡ just t → Raw.Executes s as t
replay-sound [] s refl = Raw.done
replay-sound (a ∷ as) s eq with advance a s in edge
... | nothing with eq
...   | ()
replay-sound (a ∷ as) s eq | just mid = Raw.next edge (replay-sound as mid eq)

replay-complete : ∀ {s as t} → Raw.Executes s as t → replay as s ≡ just t
replay-complete Raw.done = refl
replay-complete (Raw.next eq rest) rewrite eq = replay-complete rest

-- Acceptance returns parsed actions and endpoint; soundness ties both to the
-- designated initializer, rather than merely checking individual label syntax.
check : State → ℕ → List Char → Maybe (List Action × State)
check initial fuel cs with parse fuel cs
... | nothing = nothing
... | just as with replay as initial
...   | nothing = nothing
...   | just t = just (as , t)

check-sound : ∀ initial fuel cs {as t} →
  check initial fuel cs ≡ just (as , t) → Raw.Executes initial as t
check-sound initial fuel cs eq with parse fuel cs
... | nothing with eq
...   | ()
check-sound initial fuel cs eq | just bs with replay bs initial in run
... | nothing with eq
...   | ()
check-sound initial fuel cs refl | just bs | just t = replay-sound bs initial run

-- Printed covered real runs are accepted, with their original endpoint.
abstract
  check-complete : ∀ {s as t} (covered : Covered as dictionary) →
    Raw.Executes s as t → check s (length as) (print covered) ≡ just (as , t)
  check-complete covered run rewrite round-trip covered | replay-complete run = refl

-- A re-import certificate keeps parsed labels and the real run together.
-- This representation lets large witnesses reuse their opaque native proofs.
record Imported (initial : State) (fuel : ℕ) (cs : List Char)
  (as : List Action) (endpoint : State) : Set where
  constructor imported
  field
    parsed : parse fuel cs ≡ just as
    execution : Raw.Executes initial as endpoint

-- Such a certificate is exactly sufficient for executable checker acceptance;
-- the statement is generic so clients need not normalize a concrete replay.
abstract
  certified-acceptance : ∀ {s fuel cs as t} → Imported s fuel cs as t →
    check s fuel cs ≡ just (as , t)
  certified-acceptance (imported parsed run) rewrite parsed | replay-complete run = refl

open import Data.List.Properties using (++-identityʳ)

-- Express the scalar round trip in precisely the bridge's event carrier.
open import Process_Trees using (ExtI)
open import Data.Unit using (⊤)
open import Semantics.LTS {E = Raw.Channel} {I = ExtI Raw.Channel} using (Event√)
parseBridgeLabel : List Action → List Char → Maybe (Event√ ⊤ × List Char)
parseBridgeLabel xs cs with parseLabel xs cs
... | nothing = nothing
... | just (a , rest) = just (Raw.label a , rest)
bridge-label-round-trip : ∀ {a : Action} {xs : List Action} (p : a ∈ xs) →
  parseBridgeLabel xs (printLabel p) ≡ just (Raw.label a , [])
bridge-label-round-trip p rewrite sym (++-identityʳ (printLabel p)) | parse-print-label p [] = refl
