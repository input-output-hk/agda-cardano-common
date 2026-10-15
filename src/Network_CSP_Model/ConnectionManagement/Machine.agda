{-# OPTIONS --guardedness #-}

-- One dispatcher over the implemented rule families. This is an open, partial
-- subsystem: no rule duplication, scheduler fairness or source completeness.
module ConnectionManagement.Machine where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.IGRegistration as IG

data PublicationOutcome : Set where
  resultWritten duplicateWrite : PublicationOutcome

-- Publication outcomes are explicit; a duplicate is not a silent failed attempt.
data Action : Set where
  admissionStep : WorkerId → Server.AdmissionAction → Action
  handshakeStep : WorkerId → Handshake.HandshakeAction → Action
  cleanupStep : WorkerId → Cleanup.CleanupAction → Action
  handlerPublication : WorkerId → HandshakeResult → PublicationOutcome → Action
  handlerExit : WorkerId → Action
  igStep : IG.IGAction → Action

record Configuration : Set where
  constructor configuration
  field
    responder : ResponderMode
    world : State
    -- A throwing writer cannot publish again. The boundary may subsequently
    -- enter cleanup; rethrow policy and exception unwinding are still abstract.
    publicationFaults : List WorkerId
    inboundGovernor : IG.Runtime
open Configuration public

initial : ResponderMode → State → Configuration
initial mode s = configuration mode s [] IG.initial

replaceWorld : Configuration → State → Configuration
replaceWorld c s = record c { world = s }

advance : Action → Configuration → Maybe Configuration
advance (igStep a) c with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c))
... | nothing = nothing
... | just (ig , queue) = just (record c
  { world = record (world c) { inboundInfo = queue }; inboundGovernor = ig })
advance (admissionStep w a) c = map (replaceWorld c) (Server.stepPrefix w a (world c))
advance (handshakeStep w a) c = map (replaceWorld c) (Handshake.stepHandshake (responder c) w a (world c))
advance (cleanupStep w a) c = map (replaceWorld c) (Cleanup.stepCleanup w a (world c))
advance (handlerExit w) c = map (replaceWorld c) (Cleanup.beginCleanupBoundary w (world c))
advance (handlerPublication w result outcome) c with any (λ v → does (v ≟ w)) (publicationFaults c)
... | true = nothing
... | false with Handshake.publishBoundary w result (world c) | outcome
...   | nothing | _ = nothing
...   | just (Handshake.published s) | resultWritten = just (replaceWorld c s)
...   | just Handshake.writerBlocked | duplicateWrite =
        just (record c { publicationFaults = w ∷ publicationFaults c })
...   | _ | _ = nothing

-- Replay propagates a refused/wrong-phase attempt instead of fabricating a step.
replay : List Action → Configuration → Maybe Configuration
replay [] c = just c
replay (a ∷ as) c with advance a c
... | nothing = nothing
... | just c′ = replay as c′

data Executes : Configuration → List Action → Configuration → Set where
  done : ∀ {c} → Executes c [] c
  next : ∀ {c c₁ c₂ a as} → advance a c ≡ just c₁ → Executes c₁ as c₂ → Executes c (a ∷ as) c₂

replay-sound : ∀ as c {c′} → replay as c ≡ just c′ → Executes c as c′
replay-sound [] c refl = done
replay-sound (a ∷ as) c eq with advance a c in stepEq
... | nothing = caseImpossible eq
  where
  caseImpossible : ∀ {c′} → nothing ≡ just c′ → Executes c (a ∷ as) c′
  caseImpossible ()
... | just c₁ = next stepEq (replay-sound as c₁ eq)

replay-complete : ∀ {c as c′} → Executes c as c′ → replay as c ≡ just c′
replay-complete done = refl
replay-complete (next eq rest) rewrite eq = replay-complete rest

exec-append : ∀ {c c₁ c₂ as bs} → Executes c as c₁ → Executes c₁ bs c₂ →
  Executes c (as ++ bs) c₂
exec-append done right = right
exec-append (next eq left) right = next eq (exec-append left right)

exec-split : ∀ as {bs c c₂} → Executes c (as ++ bs) c₂ →
  Σ Configuration (λ c₁ → Executes c as c₁ × Executes c₁ bs c₂)
exec-split [] path = _ , done , path
exec-split (a ∷ as) (next eq rest) with exec-split as rest
... | c₁ , left , right = c₁ , next eq left , right

exec-deterministic : ∀ {c as c₁ c₂} → Executes c as c₁ → Executes c as c₂ → c₁ ≡ c₂
exec-deterministic done done = refl
exec-deterministic (next eq₁ left) (next eq₂ right) with just-injective (trans (sym eq₁) eq₂)
... | refl = exec-deterministic left right
