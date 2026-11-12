{-# OPTIONS --guardedness #-}

-- Exact descriptor agreement for every stored mux, exit and startup-fault row.
-- All covers traversal rows too, including rows shadowed by duplicate keys.
module ConnectionManagement.Properties.LiveTrackerCapture where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other; lookup-head)
import ConnectionManagement.Rules.MuxEgress as EgressLayout
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Properties.HandlerBirthEffects as Birth
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.OutboundRelease as OutboundRelease

import ConnectionManagement.Properties.HandlerAuxBacking as Presence
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

-- The same immutable descriptor is observed in all three record types.
record Captures (A : Set) : Set where
 field descriptor : A → S.HandlerStart
open Captures {{...}} public
instance
 mux-capture : Captures ProtocolModel.U.Frame
 mux-capture = record { descriptor = ProtocolModel.U.captured }
 exit-capture : ∀ {b} → Captures (ExitModel.Frame b)
 exit-capture {b} = record { descriptor = ExitModel.captured }
 fault-capture : ∀ {b} → Captures (UnwindModel.Fault b)
 fault-capture {b} = record { descriptor = UnwindModel.captured }

-- References compare immutable captures, never mutable continuations.
Ref : WorkerId → S.HandlerStart → Birth.Registry → Set
Ref w h registry = lookup w registry ≡ just h
Present = Presence.Present
record Covers {A : Set} {{_ : Captures A}} (rows : Store WorkerId A) (registry : Birth.Registry) : Set where
 constructor covered
 field rows-valid : All (λ { (w , row) → Ref w (descriptor row) registry }) rows
open Covers public
Retains : Birth.Registry → Birth.Registry → Set
Retains before after = ∀ w h → Ref w h before → Ref w h after
change-retains : ∀ {P before after} → Birth.Change P before after → Retains before after
change-retains {before = before} {after} change = Birth.retains {before = before} {after = after} change
covers-retained : ∀ {A : Set} {{_ : Captures A}} {rows : Store WorkerId A} {before after} → Retains before after → Covers rows before → Covers rows after
covers-retained {rows = []} retained (covered []) = covered []
covers-retained {rows = (w , row) ∷ rows} {before} {after} retained (covered (ref ∷ refs)) = covered (retained w (descriptor row) ref ∷ rows-valid (covers-retained {rows = rows} {before = before} {after = after} retained (covered refs)))
covers-empty : ∀ {A : Set} {{_ : Captures A}} registry → Covers {A} [] registry
covers-empty registry = covered []
covers-put : ∀ {A : Set} {{_ : Captures A}} w (row : A) rows registry → Ref w (descriptor row) registry → Covers rows registry → Covers (put w row rows) registry
covers-put w row [] registry ref (covered []) = covered (ref ∷ [])
covers-put w row ((q , old) ∷ rows) registry ref (covered (oldRef ∷ refs)) with w ≟ q
... | yes refl = covered (ref ∷ refs)
... | no _ = covered (oldRef ∷ rows-valid (covers-put w row rows registry ref (covered refs)))
covers-at : ∀ {A : Set} {{_ : Captures A}} {rows : Store WorkerId A} {registry} → Covers rows registry → ∀ w row → lookup w rows ≡ just row → Ref w (descriptor row) registry
covers-at {rows = []} (covered []) w row ()
covers-at {rows = (q , first) ∷ rows} {registry} (covered (ref ∷ refs)) w row found with w ≟ q
... | yes refl = case just-injective found of λ { refl → ref }
... | no _ = covers-at {rows = rows} {registry = registry} (covered refs) w row found
covers-tail : ∀ {A : Set} {{_ : Captures A}} q (row : A) rows registry → Covers ((q , row) ∷ rows) registry → Covers rows registry
covers-tail q row rows registry (covered (ref ∷ refs)) = covered refs
physical-present : ∀ w state (thread : H.Thread) → lookup w (B.threads state) ≡ just thread → Ref w (H.captured thread) (Birth.physical state)
physical-present w state thread found = trans (Birth.lookup-captures w (B.threads state)) (cong (Data.Maybe.map H.captured) found)

