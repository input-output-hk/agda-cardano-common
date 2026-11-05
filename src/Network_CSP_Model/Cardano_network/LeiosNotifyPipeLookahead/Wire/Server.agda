{-# OPTIONS --safe #-}

-- Exact server-local wire quotient; its correspondence with the detailed source is proved separately.
module Cardano_network.LeiosNotifyPipeLookahead.Wire.Server (Notification : Set) where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
open S public using (Contract; genericNext; nodeNext; Reply; normal; canceled)

-- Direction is fixed by each constructor; reply data is retained without kind abstraction.
data Wire : Set where
  request quit done : Wire
  reply : Reply → Wire

-- A next result is an application action, not a server driver Send/Receive record.
observe : S.Action → Maybe Wire
observe S.recvRequest = just request
observe S.recvQuit = just quit
observe (S.nextReply _) = nothing
observe (S.sendReply m) = just (reply m)
observe S.sendDone = just done

-- Erase only callback selections from the detailed source action list.
wire : List S.Action → List Wire
wire [] = []
wire (S.recvRequest ∷ xs) = request ∷ wire xs
wire (S.recvQuit ∷ xs) = quit ∷ wire xs
wire (S.nextReply _ ∷ xs) = wire xs
wire (S.sendReply m ∷ xs) = reply m ∷ wire xs
wire (S.sendDone ∷ xs) = done ∷ wire xs

-- Observations compose without altering the source ordering or reply fields.
wire-append : ∀ xs ys → wire (xs ++ ys) ≡ wire xs ++ wire ys
wire-append [] ys = refl
wire-append (S.recvRequest ∷ xs) ys rewrite wire-append xs ys = refl
wire-append (S.recvQuit ∷ xs) ys rewrite wire-append xs ys = refl
wire-append (S.nextReply _ ∷ xs) ys = wire-append xs ys
wire-append (S.sendReply _ ∷ xs) ys rewrite wire-append xs ys = refl
wire-append (S.sendDone ∷ xs) ys rewrite wire-append xs ys = refl

-- Cancel-only starts at the first post-Quit Canceled only for nodeNext.
data State : Set where
  Open QuitSeen CancelOnly : ℕ → State
  Closed : State

-- Fresh local server traces have no unfulfilled request and no observed Quit.
initial : State
initial = Open 0

-- Independent agency rules express unbounded request credit, exact replies and graceful Done.
data Step : Contract → State → Wire → State → Set where
  receiveRequest : ∀ {p n} → Step p (Open n) request (Open (suc n))
  receiveQuit : ∀ {p n} → Step p (Open n) quit (QuitSeen n)
  normalOpen : ∀ {p n value} → Step p (Open (suc n)) (reply (normal value)) (Open n)
  normalQuit : ∀ {p n value} → Step p (QuitSeen (suc n)) (reply (normal value)) (QuitSeen n)
  canceledOpen : ∀ {n} → Step genericNext (Open (suc n)) (reply canceled) (Open n)
  canceledQuitGeneric : ∀ {n} → Step genericNext (QuitSeen (suc n)) (reply canceled) (QuitSeen n)
  canceledQuitNode : ∀ {n} → Step nodeNext (QuitSeen (suc n)) (reply canceled) (CancelOnly n)
  canceledOnly : ∀ {p n} → Step p (CancelOnly (suc n)) (reply canceled) (CancelOnly n)
  doneQuit : ∀ {p} → Step p (QuitSeen 0) done Closed
  doneOnly : ∀ {p} → Step p (CancelOnly 0) done Closed

-- Successful lookup is proof-bearing; no payload equality or guessed finite notification basis is needed.
lookup : (p : Contract) (s : State) (e : Wire) → Maybe (Σ[ t ∈ State ] Step p s e t)
lookup p (Open n) request = just (_ , receiveRequest)
lookup p (Open n) quit = just (_ , receiveQuit)
lookup p (Open (suc n)) (reply (normal value)) = just (_ , normalOpen)
lookup p (QuitSeen (suc n)) (reply (normal value)) = just (_ , normalQuit)
lookup genericNext (Open (suc n)) (reply canceled) = just (_ , canceledOpen)
lookup genericNext (QuitSeen (suc n)) (reply canceled) = just (_ , canceledQuitGeneric)
lookup nodeNext (QuitSeen (suc n)) (reply canceled) = just (_ , canceledQuitNode)
lookup p (CancelOnly (suc n)) (reply canceled) = just (_ , canceledOnly)
lookup p (QuitSeen zero) done = just (_ , doneQuit)
lookup p (CancelOnly zero) done = just (_ , doneOnly)
lookup _ _ _ = nothing

-- Every independently permitted step has exactly the target returned by lookup.
lookup-complete : ∀ {p s e t} (pr : Step p s e t) → lookup p s e ≡ just (t , pr)
lookup-complete receiveRequest = refl
lookup-complete receiveQuit = refl
lookup-complete normalOpen = refl
lookup-complete normalQuit = refl
lookup-complete canceledOpen = refl
lookup-complete canceledQuitGeneric = refl
lookup-complete canceledQuitNode = refl
lookup-complete canceledOnly = refl
lookup-complete doneQuit = refl
lookup-complete doneOnly = refl

-- Finite prefixes accept EOF with remaining obligations rather than pretending successful completion.
data Run (p : Contract) : State → List Wire → State → Set where
  stop : ∀ {s} → Run p s [] s
  step : ∀ {s t u e es} → Step p s e t → Run p t es u → Run p s (e ∷ es) u

-- The acceptance proposition retains an actual finite quotient execution and its target.
HasTrace : Contract → State → List Wire → Set
HasTrace p s rows = Σ[ t ∈ State ] Run p s rows t

-- Structural recursion on input yields sound acceptance and exhaustive rejection for this quotient.
decide : (p : Contract) (s : State) (rows : List Wire) → Dec (HasTrace p s rows)
decide p s [] = yes (_ , stop)
decide p s (row ∷ rows) with lookup p s row in found
... | just (next , pr) with decide p next rows
...   | yes (last , rest) = yes (last , step pr rest)
...   | no deny = no λ { (_ , step actual rest) → bad actual rest }
  where
  -- Lookup completeness identifies the unique target before applying the suffix refutation.
  bad : ∀ {t u} → Step p s row t → Run p t rows u → ⊥
  bad actual rest with trans (sym found) (lookup-complete actual)
  ... | refl = deny (_ , rest)
decide p s (row ∷ rows) | nothing = no λ { (_ , step pr rest) → impossible (trans (sym found) (lookup-complete pr)) }
  where
  -- An independently valid rule cannot have a missing lookup result.
  impossible : ∀ {t} {pr : Step p s row t} → nothing ≡ just (t , pr) → ⊥
  impossible ()
