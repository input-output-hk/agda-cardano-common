{-# OPTIONS --guardedness #-}

-- Two overlapping success invocations, starting from an explicit resource fixture.
-- This fixture is not a proof of a two-admission source-reachable prefix.
module ConnectionManagement.Negative.OriginRegistry where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing; fromMaybe)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Store using (put)
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action; allocate; dispatch)
open import ConnectionManagement.Properties.HandlerResources using (Resources)
import ConnectionManagement.Properties.OriginRegistry as Proof
open import ConnectionManagement.CSP.OriginRegistry
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)
import ConnectionManagement.Negative.AttributedOrigin

worker₂ : WorkerId
worker₂ = ident 3
handler₂ : S.HandlerStart
handler₂ = S.handlerStart (ident 0) (ident 1) (ident 1) key₀
both : Open.Configuration
both = record E.forked { world = record (Open.world E.forked)
  { handlers = put worker₂ handler₂ (S.handlers (Open.world E.forked))
  ; sockets = put (ident 1) (S.handling worker₂) (S.sockets (Open.world E.forked))
  ; promises = ident 0 ∷ ident 1 ∷ []; nextPromise = 2 } }

alloc₁ alloc₂ publish₁ publish₂ : Action
alloc₁ = allocate child₀ (ident 0) (ident 0) key₀ (G.proto ∷ []) duplex
alloc₂ = allocate worker₂ (ident 1) (ident 1) key₀ (G.proto ∷ []) duplex
publish₁ = dispatch (Open.handlerPublication child₀ (S.negotiated (ident 0) duplex) Open.resultWritten)
publish₂ = dispatch (Open.handlerPublication worker₂ (S.negotiated (ident 1) duplex) Open.resultWritten)

-- Computed snapshots are independently checked by the successful-step equations.
after : Action → State → State
after a s = fromMaybe s (step a s)
s₀ s₁ s₂ s₃ s₄ : State
s₀ = start both
s₁ = after alloc₁ s₀
s₂ = after alloc₂ s₁
s₃ = after publish₂ s₂
s₄ = after publish₁ s₃
schedule : List Action
schedule = alloc₁ ∷ alloc₂ ∷ publish₂ ∷ publish₁ ∷ []
path : Executes s₀ schedule s₄
path = next {s₁ = s₁} refl (next {s₁ = s₂} refl (next {s₁ = s₃} refl (next refl done)))
prefix : Executes s₀ (alloc₁ ∷ alloc₂ ∷ []) s₂
prefix = next {s₁ = s₁} refl (next refl done)
accepted : traces (Process s₀) (map label schedule)
accepted = trace-intro path

-- Both workers have explicit heap resources at their respective allocations.
first-resources : Resources child₀ (Open.world both)
first-resources = record
  { original = S.handlerStart (ident 0) (ident 0) (ident 0) key₀
  ; found = refl; entryExists = _ , refl; socketExists = _ , refl }
second-resources : Resources worker₂ (Open.world (machine s₁))
second-resources = record
  { original = handler₂; found = refl; entryExists = _ , refl; socketExists = _ , refl }
supported : Proof.Supported path
supported = Proof.next first-resources (Proof.next second-resources (Proof.next tt (Proof.next tt Proof.done)))
all-certified : Proof.Invariant s₄
all-certified = Proof.reachable path supported

-- Same captured key does not let one worker publish another worker's handle.
swap : Action
swap = dispatch (Open.handlerPublication child₀ (S.negotiated (ident 1) duplex) Open.resultWritten)
swap-refused : step swap s₂ ≡ nothing
swap-refused = refl
no-swap : ¬ traces (Process s₀) (map label (alloc₁ ∷ alloc₂ ∷ swap ∷ []))
no-swap = refused-extension prefix swap-refused

unregistered-refused : step publish₁ s₀ ≡ nothing
unregistered-refused = refl
no-unregistered : ¬ traces (Process s₀) (map label (publish₁ ∷ []))
no-unregistered = refused-extension {as = []} done unregistered-refused
worker-reuse-refused : step (allocate child₀ (ident 2) (ident 2) key₀ (G.proto ∷ []) duplex) s₁ ≡ nothing
worker-reuse-refused = refl
handle-reuse-refused : step (allocate worker₂ (ident 0) (ident 1) key₀ (G.proto ∷ []) duplex) s₁ ≡ nothing
handle-reuse-refused = refl

import ConnectionManagement.Rules.OriginMonitor as Single
import ConnectionManagement.Rules.IGRegistration as IG

-- The final invariant covers two concrete published entries, not an empty list.
two-published : entries s₄ ≡
  entry (Single.target worker₂ (ident 1)) (Single.published (Single.ticket (ident 1) (G.proto ∷ []) duplex)) ∷
  entry (Single.target child₀ (ident 0)) (Single.published (Single.ticket (ident 0) (G.proto ∷ []) duplex)) ∷ []
two-published = refl
raw-empty-refused : step (dispatch (Open.igStep (IG.installHandle (ident 0) (ident 0) key₀ (G.proto ∷ []) duplex))) s₀ ≡ nothing
raw-empty-refused = refl
flow-mismatch-refused : step (dispatch (Open.handlerPublication child₀ (S.negotiated (ident 0) unidirectional) Open.resultWritten)) s₂ ≡ nothing
flow-mismatch-refused = refl
