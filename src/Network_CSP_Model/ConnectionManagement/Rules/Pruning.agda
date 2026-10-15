{-# OPTIONS --guardedness #-}

-- Core.hs:720-777 and Diffusion/Policies.hs:284-306 at network
-- 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d. Random Int scores are explicit
-- order inputs, not a bit-level implementation of StdGen/randoms.
module ConnectionManagement.Rules.Pruning where

open import Data.Bool using (Bool; true; false; not)
open import Data.Nat using (ℕ; _<?_)
open import Data.Integer using (ℤ) renaming (_<?_ to _<ℤ?_)
open import Data.List using (List; []; _∷_; _++_; map; take; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; does)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.ConnectionOrder using (keyLess)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Rules.InboundRelease as Release

record Candidate : Set where
  constructor candidate
  field connectionKey : ConnectionKey
        entryRef : EntryId
        thread : WorkerId
        -- Ord ConnectionType restricted to eligible inbound candidates.
        typeRank : ℕ
        upstream : Bool
open Candidate public

candidateFor : ConnectionKey → EntryId → ConnectionState → Maybe Candidate
candidateFor k e (unnegotiated inbound _ w) = just (candidate k e w 0 false)
candidateFor k e (inboundIdle _ w _ unidirectional) = just (candidate k e w 1 false)
candidateFor k e (inboundIdle _ w _ duplex) = just (candidate k e w 2 false)
candidateFor k e (inboundActive _ w _ unidirectional) = just (candidate k e w 3 false)
candidateFor k e (inboundActive _ w _ duplex) = just (candidate k e w 4 false)
candidateFor k e (duplexActive _ w _) = just (candidate k e w 5 true)
candidateFor _ _ _ = nothing

-- State.toMap omits unknown-local bindings; read every remaining entry.
innerCandidates : PeerAddr → Store LocalKey EntryId → EntryHeap → Maybe (List Candidate)
innerCandidates r [] heap = just []
innerCandidates r ((unknownLocal , _) ∷ rest) heap = innerCandidates r rest heap
innerCandidates r ((knownLocal l , e) ∷ rest) heap with lookup e heap | innerCandidates r rest heap
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just st | just cs with candidateFor (connection l r) e st
...   | nothing = just cs
...   | just c = just (c ∷ cs)

candidates : ConnMap → EntryHeap → Maybe (List Candidate)
candidates [] heap = just []
candidates ((r , inner) ∷ rest) heap with innerCandidates r inner heap | candidates rest heap
... | just cs | just ds = just (cs ++ ds)
... | _ | _ = nothing

-- Stable insertion sort: insert before equal keys, preserving input tie order.
insertBy : ∀ {A : Set} → (A → A → Bool) → A → List A → List A
insertBy less x [] = x ∷ []
insertBy less x (y ∷ ys) with less y x
... | true = y ∷ insertBy less x ys
... | false = x ∷ y ∷ ys
sortBy : ∀ {A : Set} → (A → A → Bool) → List A → List A
sortBy less [] = []
sortBy less (x ∷ xs) = insertBy less x (sortBy less xs)

-- Map.insert of the prospective connection overrides the old candidate by KEY.
withProspective : Candidate → List Candidate → List Candidate
withProspective c cs = c ∷ filterᵇ (λ old → not (does (connectionKey old ≟ connectionKey c))) cs
byKey : Candidate → Candidate → Bool
byKey c d = keyLess (connectionKey c) (connectionKey d)

Scored = Candidate × ℤ
scoreLess : Scored → Scored → Bool
scoreLess (c , x) (d , y) with upstream c | upstream d
... | false | true = true
... | true | false = false
... | _ | _ with x <ℤ? y | y <ℤ? x
...   | yes _ | _ = true
...   | no _ | yes _ = false
...   | no _ | no _ = does (typeRank c <? typeRank d)

-- Exactly one score per Map.assocs entry, assigned BEFORE policy sorting.
attachScores : List Candidate → List ℤ → Maybe (List Scored)
attachScores [] [] = just []
attachScores (c ∷ cs) (x ∷ xs) with attachScores cs xs
... | nothing = nothing
... | just rest = just ((c , x) ∷ rest)
attachScores _ _ = nothing

containsKey : ConnectionKey → List Candidate → Bool
containsKey k [] = false
containsKey k (c ∷ cs) with k ≟ connectionKey c
... | yes _ = true
... | no _ = containsKey k cs

record Plan : Set where
  constructor plan
  field choices victims : List Candidate
        edits : List (EntryId × ConnectionState)
open Plan public

makePlan : ℕ → Candidate → ConnectionState → List Candidate → List ℤ → Maybe Plan
makePlan n self nextState cs scores with attachScores ordered scores
  where ordered = sortBy byKey (withProspective self cs)
... | nothing = nothing
... | just ranked = just (plan ordered selected writes)
  where
  ordered = sortBy byKey (withProspective self cs)
  winners = map proj₁ (take n (sortBy scoreLess ranked))
  -- restrictKeys preserves MAP order, not policy-score order.
  selected = filterᵇ (λ c → containsKey (connectionKey c) winners) ordered
  promotion : List (EntryId × ConnectionState)
  promotion with containsKey (connectionKey self) winners
  ... | true = []
  ... | false = (entryRef self , nextState) ∷ []
  writes = map (λ c → entryRef c , terminated nothing) selected ++ promotion

-- A list of writes is one atomic machine effect; failure publishes no prefix.
applyEdits : List (EntryId × ConnectionState) → State → Maybe State
applyEdits [] s = just s
applyEdits (edit ∷ edits) s with Release.applyEdit (just edit) s
... | nothing = nothing
... | just s′ = applyEdits edits s′
