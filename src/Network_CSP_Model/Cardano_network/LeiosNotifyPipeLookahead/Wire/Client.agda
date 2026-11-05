{-# OPTIONS --safe #-}

-- Exact generic successful-callback client driver-hook language, including delayed Send.
module Cardano_network.LeiosNotifyPipeLookahead.Wire.Client (Notification : Set) where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
open S public using (Reply; normal; canceled)

-- Direction is fixed: requests/Quit are Sends and replies/Done are Receives.
data Wire : Set where
  request quit done : Wire
  reply : Reply → Wire

-- Callback choices and successful handling are not driver log records.
module Observation (Return : Set) where
  import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C

  -- Preserve every exact reply value while deleting only local callback actions.
  observe : C.Action → Maybe Wire
  observe C.sendRequest = just request
  observe C.sendQuit = just quit
  observe (C.recvReply m) = just (reply m)
  observe C.recvDone = just done
  observe _ = nothing

  -- Projection retains source action order, including a Receive before delayed Send.
  wire : List C.Action → List Wire
  wire [] = []
  wire (C.sendRequest ∷ xs) = request ∷ wire xs
  wire (C.sendQuit ∷ xs) = quit ∷ wire xs
  wire (C.recvReply m ∷ xs) = reply m ∷ wire xs
  wire (C.recvDone ∷ xs) = done ∷ wire xs
  wire (C.continue _ ∷ xs) = wire xs
  wire (C.terminate _ ∷ xs) = wire xs
  wire (C.handled _ ∷ xs) = wire xs

  -- Source concatenation preserves the same concatenation of exact hook observations.
  wire-append : ∀ xs ys → wire (xs ++ ys) ≡ wire xs ++ wire ys
  wire-append [] ys = refl
  wire-append (C.sendRequest ∷ xs) ys rewrite wire-append xs ys = refl
  wire-append (C.sendQuit ∷ xs) ys rewrite wire-append xs ys = refl
  wire-append (C.recvReply _ ∷ xs) ys rewrite wire-append xs ys = refl
  wire-append (C.recvDone ∷ xs) ys rewrite wire-append xs ys = refl
  wire-append (C.continue _ ∷ xs) ys = wire-append xs ys
  wire-append (C.terminate _ ∷ xs) ys = wire-append xs ys
  wire-append (C.handled _ ∷ xs) ys = wire-append xs ys

-- Lead is the single registered response received before its Request Send hook.
data State : Set where
  Open QuitSeen : ℕ → State
  Lead Closed : State

-- Fresh logs begin with no reply credit and no shutdown observed.
initial : State
initial = Open 0

-- Generic callbacks impose no fixed depth and successfully handle either exact reply kind.
data Step : State → Wire → State → Set where
  sendRequest : ∀ {n} → Step (Open n) request (Open (suc n))
  finishRequest : Step Lead request (Open 0)
  receiveReply : ∀ {n m} → Step (Open (suc n)) (reply m) (Open n)
  earlyReply : ∀ {m} → Step (Open 0) (reply m) Lead
  sendQuit : ∀ {n} → Step (Open n) quit (QuitSeen n)
  drainReply : ∀ {n m} → Step (QuitSeen (suc n)) (reply m) (QuitSeen n)
  receiveDone : Step (QuitSeen 0) done Closed

-- Deterministic rule lookup retains a proof and does not require notification equality.
lookup : (s : State) (e : Wire) → Maybe (Σ[ t ∈ State ] Step s e t)
lookup (Open n) request = just (_ , sendRequest)
lookup Lead request = just (_ , finishRequest)
lookup (Open (suc n)) (reply m) = just (_ , receiveReply)
lookup (Open 0) (reply m) = just (_ , earlyReply)
lookup (Open n) quit = just (_ , sendQuit)
lookup (QuitSeen (suc n)) (reply m) = just (_ , drainReply)
lookup (QuitSeen 0) done = just (_ , receiveDone)
lookup _ _ = nothing

-- Every independent rule is returned by lookup with precisely its own target.
lookup-complete : ∀ {s e t} (pr : Step s e t) → lookup s e ≡ just (t , pr)
lookup-complete sendRequest = refl
lookup-complete finishRequest = refl
lookup-complete receiveReply = refl
lookup-complete earlyReply = refl
lookup-complete sendQuit = refl
lookup-complete drainReply = refl
lookup-complete receiveDone = refl

-- Finite prefixes accept EOF with remaining obligations rather than pretending successful completion.
data Run : State → List Wire → State → Set where
  stop : ∀ {s} → Run s [] s
  step : ∀ {s t u e es} → Step s e t → Run t es u → Run s (e ∷ es) u

-- The acceptance proposition retains an actual finite quotient execution and its target.
HasTrace : State → List Wire → Set
HasTrace s rows = Σ[ t ∈ State ] Run s rows t

-- Structural recursion on input yields sound acceptance and exhaustive rejection for this quotient.
decide : (s : State) (rows : List Wire) → Dec (HasTrace s rows)
decide s [] = yes (_ , stop)
decide s (row ∷ rows) with lookup s row in found
... | just (next , pr) with decide next rows
...   | yes (last , rest) = yes (last , step pr rest)
...   | no deny = no λ { (_ , step actual rest) → bad actual rest }
  where
  -- Lookup completeness identifies the unique target before applying the suffix refutation.
  bad : ∀ {t u} → Step s row t → Run t rows u → ⊥
  bad actual rest with trans (sym found) (lookup-complete actual)
  ... | refl = deny (_ , rest)
decide s (row ∷ rows) | nothing = no λ { (_ , step pr rest) → impossible (trans (sym found) (lookup-complete pr)) }
  where
  -- An independently valid rule cannot have a missing lookup result.
  impossible : ∀ {t} {pr : Step s row t} → nothing ≡ just (t , pr) → ⊥
  impossible ()
