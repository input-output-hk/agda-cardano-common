{-# OPTIONS --safe #-}

-- Concrete successful unit-return client examples and exhaustive initial-prefix rejection.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientTests where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Bool as Q
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientQuotient Bool ⊤ as Proof
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientComplete Bool ⊤ tt as Realize

-- A reply Receive can precede the Send hook of its physically committed RequestNext.
receive-before-send : Proof.SourceTrace
  (Q.reply (Q.normal true) ∷ Q.request ∷ Q.quit ∷ Q.done ∷ [])
receive-before-send = toWitness {a? = Proof.decide-source tt _} tt

-- Prefix EOF can stop immediately after the early Receive with its Send still pending.
early-eof : Proof.SourceTrace (Q.reply (Q.normal false) ∷ [])
early-eof = toWitness {a? = Proof.decide-source tt _} tt

-- Generic successful handlers may process Canceled before Quit; node callback failure is separate.
generic-canceled : Proof.SourceTrace
  (Q.reply Q.canceled ∷ Q.request ∷ Q.quit ∷ Q.done ∷ [])
generic-canceled = toWitness {a? = Proof.decide-source tt _} tt

-- Multiple exact payloads survive pipelining and graceful cancellation drain.
exact-pipeline : Proof.SourceTrace
  (Q.request ∷ Q.request ∷ Q.quit ∷ Q.reply (Q.normal true) ∷ Q.reply Q.canceled ∷ Q.done ∷ [])
exact-pipeline = toWitness {a? = Proof.decide-source tt _} tt

-- Idle shutdown realizes the real no-marker path using the supplied unit return value.
idle-close : Proof.SourceTrace (Q.quit ∷ Q.done ∷ [])
idle-close = toWitness {a? = Proof.decide-source tt _} tt

-- With one old request, another registered Request may receive before its Send hook.
second-receive-ahead : Proof.SourceTrace
  (Q.request ∷ Q.reply (Q.normal true) ∷ Q.reply (Q.normal false) ∷ Q.request ∷ [])
second-receive-ahead = toWitness {a? = Proof.decide-source tt _} tt

-- At most one unrecorded Request is registered, so two leading replies are impossible.
two-leading-replies : Proof.SourceTrace
  (Q.reply (Q.normal true) ∷ Q.reply (Q.normal false) ∷ []) → ⊥
two-leading-replies = toWitnessFalse {a? = Proof.decide-source tt _} tt

-- The main thread cannot issue Quit while its pending Request Send hook has not returned.
quit-with-pending-send : Proof.SourceTrace
  (Q.reply (Q.normal true) ∷ Q.quit ∷ []) → ⊥
quit-with-pending-send = toWitnessFalse {a? = Proof.decide-source tt _} tt

-- Done requires a recorded Quit and exhaustion of every actual reply obligation.
premature-done : Proof.SourceTrace (Q.request ∷ Q.quit ∷ Q.done ∷ []) → ⊥
premature-done = toWitnessFalse {a? = Proof.decide-source tt _} tt

-- Initial Done is not a shutdown witness.
initial-done : Proof.SourceTrace (Q.done ∷ []) → ⊥
initial-done = toWitnessFalse {a? = Proof.decide-source tt _} tt

-- A client that has sent Quit never sends a fresh RequestNext.
request-after-quit : Proof.SourceTrace (Q.quit ∷ Q.request ∷ []) → ⊥
request-after-quit = toWitnessFalse {a? = Proof.decide-source tt _} tt

-- Quit is emitted at most once in a successful finite client execution.
repeated-quit : Proof.SourceTrace (Q.quit ∷ Q.quit ∷ []) → ⊥
repeated-quit = toWitnessFalse {a? = Proof.decide-source tt _} tt

-- Accepted EOF remains an unclosed quotient prefix with one reply obligation outstanding.
unfinished-target : Q.Run Q.initial (Q.request ∷ Q.quit ∷ []) (Q.QuitSeen 1)
unfinished-target = Q.step Q.sendRequest (Q.step Q.sendQuit Q.stop)
