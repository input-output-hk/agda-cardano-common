{-# OPTIONS --guardedness #-}

-- The bookkeeping family is reachable in the actual new PTree, not only its rules.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NativeReachability where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Unit using (tt)
open import Level using (lift)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (ExtI; fin)
open import Cardano_network.Base using (hi; FromInitiator)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams using (leiosNotifyP; MsgLNPRequestNext; MsgLNPVotes)
open import Cardano_network.Net replayParams using (lnpSendVotes)
open import Cardano_network.LeiosNotifyP replayParams using (LNPEv; receiveLNP; sendLNP; apiLPev)
import Cardano_network.LeiosNotifyPipeLookahead replayParams as Native
open Native.Reference
open Native.Machine nodeNext fzero hi
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.Replay.Bridge {E = LNPEv} {I = ExtI LNPEv} using (⟹∖√-++)

-- One native reply value suffices for the constructive reachability family.
requestEvent : LTS.Event
requestEvent = LTS.evLabel _ (receiveLNP fzero hi)
  (tt , FromInitiator , tt , leiosNotifyP MsgLNPRequestNext)

-- Application readiness provides exactly the native payload subsequently sent.
readyEvent : LTS.Event
readyEvent = LTS.evLabel _ (apiLPev fzero hi lnpSendVotes) []

-- The native sender forwards that same value on its wire channel.
replyEvent : LTS.Event
replyEvent = LTS.evLabel _ (sendLNP fzero hi) (packet (MsgLNPVotes []))

-- Already answered requests leave completion tokens until a future Quit.
readyState : ℕ → State
readyState n = state awaitNext 0 idle n false

-- A complete exchange has two wire observations and one application event.
roundEvents : List LTS.Event
roundEvents = requestEvent ∷ readyEvent ∷ replyEvent ∷ []

-- Every admission/register/claim/send/retire operation is an actual PTree move.
after-request : (n : ℕ) → tree (state admit 0 idle n false)
  ⟹∖√⟨ readyEvent ∷ replyEvent ∷ [] ⟩ tree (readyState (suc n))
after-request n =
  ∖√-τ (LTS.sTau {i = (_ , fin {n = 2})} {a = lift fzero} refl refl) $
  ∖√-τ (LTS.sTau {i = (_ , fin {n = 1})} {a = lift fzero} refl refl) $
  ∖√-τ (LTS.sTau {i = (_ , fin {n = 1})} {a = lift fzero} refl refl) $
  ∖√-ev (LTS.sVis refl refl) $
  ∖√-ev (LTS.sVis refl refl) $
  ∖√-τ (LTS.sTau {i = (_ , fin {n = 1})} {a = lift fzero} refl refl) ∖√-refl

-- The fresh source server can execute its first ordinary exchange.
first-round : tree initial ⟹∖√⟨ roundEvents ⟩ tree (readyState 1)
first-round = ∖√-ev (LTS.sVis refl refl) (after-request 0)

-- The reader can repeat an exchange without collecting the completion tokens.
next-round : (n : ℕ) → tree (readyState n) ⟹∖√⟨ roundEvents ⟩ tree (readyState (suc n))
next-round n = ∖√-ev (LTS.sVis refl refl) (after-request n)

-- Arbitrarily large bookkeeping states have inhabited finite native executions.
completed-native : (n : ℕ) → Σ[ es ∈ List LTS.Event ]
  tree initial ⟹∖√⟨ es ⟩ tree (readyState (suc n))
completed-native zero = roundEvents , first-round
completed-native (suc n) with completed-native n
... | es , run = es ++ roundEvents , ⟹∖√-++ run (next-round (suc n))

-- These reachable native states have no unanswered requests.
ready-owed : ∀ n → owed (readyState n) ≡ 0
ready-owed n = refl
