{-# OPTIONS --guardedness #-}

-- Resource consequences of actual outbound physical births. Capture ownership
-- is derived from the absent-before row; the outer event is never relabeled.
module ConnectionManagement.Properties.OutboundBirthResources where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; EntryId; PromiseId; ConnectionKey; ErrorId; HandleId)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.Counters using (lookup-all)
open import ConnectionManagement.Properties.HandlerResourceFacts using (Facts)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.Properties.HandlerBirthBacking as Birth
import ConnectionManagement.Properties.HandlerBirthEffects as Effects
import ConnectionManagement.Properties.InboundBirthLabels as Labels
import ConnectionManagement.Properties.ServerPeersHandlerResources as Resources
import ConnectionManagement.Properties.OutboundCapture as Capture
import ConnectionManagement.Properties.InboundOriginRuntime as Runtime

private
 -- Counter/other continuations cannot perform forkOK.
 fork-continuation : ∀ caller mode savedFrame world {out} →
   A.step caller mode A.forkOK savedFrame world ≡ just out →
   Σ EntryId (λ entry → Σ PromiseId (λ promise → Σ ConnectionKey (λ key →
     A.pc savedFrame ≡ A.forkHandler entry promise key)))
 fork-continuation caller mode savedFrame world actual with A.pc savedFrame
 ... | A.forkHandler entry promise key = entry , promise , key , refl
 ... | A.selecting = case actual of λ ()
 ... | A.count next = case actual of λ ()
 ... | A.allocatePromise entry = case actual of λ ()
 ... | A.openSocket entry promise = case actual of λ ()
 ... | A.configureSocket entry promise = case actual of λ ()
 ... | A.bindSocket entry promise = case actual of λ ()
 ... | A.connectSocket entry promise = case actual of λ ()
 ... | A.localAddress entry promise = case actual of λ ()
 ... | A.updateAddress entry promise key = case actual of λ ()
 ... | A.connectedCommit entry promise key = case actual of λ ()
 ... | A.awaitResult entry promise key = case actual of λ ()
 ... | A.commitResult entry key result = case actual of λ ()
 ... | A.waitingInbound entry key = case actual of λ ()
 ... | A.closeError entry fault = case actual of λ ()
 ... | A.removeError entry fault = case actual of λ ()
 ... | A.complete result = case actual of λ ()

 fork-PC : ∀ caller before {after} → O.advance (O.acquire caller A.forkOK) before ≡ just after →
   Σ A.Request (λ request → Σ EntryId (λ entry → Σ PromiseId (λ promise → Σ ConnectionKey (λ key →
     lookup caller (O.acquiring before) ≡ just (A.frame request (A.forkHandler entry promise key))))))
 fork-PC caller before actual with lookup caller (O.acquiring before) in found
 ... | nothing = case actual of λ ()
 ... | just savedFrame with A.step caller (M.responder (O.core before)) A.forkOK savedFrame (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just pair with fork-continuation caller (M.responder (O.core before)) savedFrame (M.world (O.core before)) stepped
 ...     | entry , promise , key , pc = A.req savedFrame , entry , promise , key ,
   cong just (cong (A.frame (A.req savedFrame)) pc)

 -- Only the fresh written key can explain the queried new capture.
 put-identifies : ∀ (writer queried : WorkerId) (descriptor : S.HandlerStart)
   (registry : Effects.Registry) (captured : S.HandlerStart) →
   lookup queried registry ≡ nothing → lookup queried (put writer descriptor registry) ≡ just captured →
   queried ≡ writer × descriptor ≡ captured
 put-identifies writer queried descriptor registry captured absent found with queried ≟ writer
 ... | yes refl = refl , just-injective (trans (sym (lookup-put writer descriptor registry)) found)
 ... | no different = case trans (sym absent)
   (trans (sym (lookup-put-other writer queried descriptor registry different)) found) of λ ()

 fork-installed : ∀ caller request entry promise key before {after} →
   lookup caller (O.acquiring before) ≡ just (A.frame request (A.forkHandler entry promise key)) →
   O.advance (O.acquire caller A.forkOK) before ≡ just after →
   lookup (A.child request) (S.handlers (M.world (O.core after))) ≡ just (S.handlerStart entry (A.socketRef request) promise key)
 fork-installed caller request entry promise key before owned actual rewrite owned
   with lookup (A.child request) (S.handlers (M.world (O.core before)))
 ... | just old = case actual of λ ()
 ... | nothing with just-injective actual
 ...   | refl = lookup-put (A.child request) _ (S.handlers (M.world (O.core before)))

 record RawOwner (caller : WorkerId) (before after : B.State) (queried : WorkerId) (captured : S.HandlerStart) : Set where
  field
   request : A.Request
   entry : EntryId
   promise : PromiseId
   key : ConnectionKey
   before-PC : lookup caller (O.acquiring (B.source before)) ≡ just (A.frame request (A.forkHandler entry promise key))
   source-step : O.advance (O.acquire caller A.forkOK) (B.source before) ≡ just (B.source after)
   worker : queried ≡ A.child request
   descriptor : captured ≡ S.handlerStart entry (A.socketRef request) promise key

 raw-owner : ∀ caller before {after queried captured} →
   B.forkOutbound caller before ≡ just after →
   lookup queried (Effects.physical before) ≡ nothing → lookup queried (Effects.physical after) ≡ just captured →
   RawOwner caller before after queried captured
 raw-owner caller before {queried = queried} {captured} actual absent found
   with lookup caller (O.acquiring (B.source before)) in owned
 ... | nothing = case actual of λ ()
 ... | just savedFrame with B.freshChild (A.child (A.req savedFrame)) before
 ...   | false = case actual of λ ()
 ...   | true with O.advance (O.acquire caller A.forkOK) (B.source before) in advanced
 ...     | nothing = case actual of λ ()
 ...     | just next with lookup (A.child (A.req savedFrame)) (S.handlers (M.world (O.core next))) in installed
 ...       | nothing = case actual of λ ()
 ...       | just handler with just-injective actual
 ...         | refl with fork-PC caller (B.source before) advanced
 ...           | request , entry , promise , key , beforePC with just-injective (trans (sym owned) beforePC)
 ...             | refl with put-identifies (A.child request) queried handler (Effects.physical before) captured absent
   (trans (sym (cong (lookup queried) (Effects.captures-put (A.child request) (H.handlerThread handler H.maskedSetup) (B.threads before)))) found)
 ...               | workerEq , captureEq = record
   { request = request; entry = entry; promise = promise; key = key; before-PC = beforePC; source-step = advanced
   ; worker = workerEq; descriptor = trans (sym captureEq)
     (just-injective (trans (sym installed) (fork-installed caller request entry promise key (B.source before) beforePC advanced))) }

 -- This eliminator reduces only the already classified outer sum.
 Left : ∀ {X Y : Set} → X ⊎ Y → Set
 Left {X} (inj₁ x) = X
 Left (inj₂ y) = ⊤
 left : ∀ {X Y : Set} (sum : X ⊎ Y) → Left sum
 left (inj₁ x) = x
 left (inj₂ y) = tt

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 private
  module T = Combined.Protocols b io capability using (Runtime; Event; Runs; base; initialize)
  module K = Combined b io using (source)
  module Back = Birth.Frontend b io capability using (Backing; ForkStep; fork-step; physical-state; view)
  module History = Birth.Frontend.LocatedSearch.Located b io capability using (before; after; action; actual; selected; absent-before; at-birth)
  module Label = Labels.Frontend b io capability using (Inbound; SourceFork; actual-source; operation-owner)
  module FS = Labels.Frontend.SourceFork using (operation; source-after)
  module View = Runtime.Frontend b io capability using (core; shared)
  module Old = Resources b io using (outbound-fork-facts)
  module Captures = Resources.Frontend b io capability using (initialized-frontend-captures)
 open View public using (core; shared)
 source : T.Runtime → O.Configuration
 source state = K.source (T.base state)

 -- The actual raw target supplies acquisition data; source-after relates its
 -- logical heap to the identical outer birth, including coupled bookkeeping.
 record Outbound (before born : T.Runtime) (queried : WorkerId) (captured : S.HandlerStart) : Set where
  field
   caller : WorkerId
   request : A.Request
   entry : EntryId
   promise : PromiseId
   key : ConnectionKey
   physical-target : B.State
   enabled : B.step (B.outbound (O.acquire caller A.forkOK)) (Back.physical-state before) ≡ just physical-target
   before-PC : lookup caller (O.acquiring (source before)) ≡ just (A.frame request (A.forkHandler entry promise key))
   source-step : O.advance (O.acquire caller A.forkOK) (source before) ≡ just (B.source physical-target)
   core-after : O.core (B.source physical-target) ≡ core born
   worker : queried ≡ A.child request
   descriptor : captured ≡ S.handlerStart entry (A.socketRef request) promise key

 private
  owner : ∀ before born {registry queried captured}
    (operation : Back.ForkStep (Back.physical-state before) registry) →
    O.core (B.source (Back.ForkStep.target operation)) ≡ core born →
    lookup queried (Effects.physical (Back.physical-state before)) ≡ nothing →
    lookup queried (Effects.physical (Back.ForkStep.target operation)) ≡ just captured →
    Label.Inbound before born queried captured ⊎ Outbound before born queried captured
  owner before born operation@(Back.fork-step command target enabled (Effects.inbound-physical parent) same) sourceAfter absent found =
    inj₁ (left (Label.operation-owner before born operation sourceAfter absent found))
  owner before born (Back.fork-step command target enabled (Effects.outbound-physical caller) same) sourceAfter absent found = inj₂ (record
    { caller = caller; request = RawOwner.request raw; entry = RawOwner.entry raw
    ; promise = RawOwner.promise raw; key = RawOwner.key raw; physical-target = target; enabled = enabled
    ; before-PC = RawOwner.before-PC raw; source-step = RawOwner.source-step raw; core-after = sourceAfter
    ; worker = RawOwner.worker raw; descriptor = RawOwner.descriptor raw })
    where raw = raw-owner caller (Back.physical-state before) enabled absent found

 classify : ∀ {start current events queried captured} (history : Back.Backing start current events queried captured) →
   Label.Inbound (History.before (Back.Backing.location history)) (History.after (Back.Backing.location history)) queried captured ⊎
   Outbound (History.before (Back.Backing.location history)) (History.after (Back.Backing.location history)) queried captured
 classify {queried = queried} history = owner (History.before location) (History.after location)
   (FS.operation observation) (FS.source-after observation) (History.absent-before location)
   (trans (cong (lookup queried) (Back.ForkStep.captures-after (FS.operation observation))) (History.at-birth location))
   where
   location = Back.Backing.location history
   observation = Label.actual-source (History.action location) (History.before location) (History.actual location) (History.selected location)

 -- The explicit O.initial profile supplies all active-savedFrame entry captures.
 -- No entry/promise heap emptiness or live map ownership premise is introduced.
 resources : ∀ {input governor start prefix before born queried captured} →
   T.initialize (O.initial input) governor ≡ just start → T.Runs start prefix before →
   Outbound before born queried captured → Facts queried captured (shared born)
 resources {input} {governor} {start} {prefix} {before} {born} {queried} {captured} initialized path birth =
   subst (λ worker → Facts worker captured (shared born)) (sym (Outbound.worker birth))
     (subst (λ descriptor → Facts (A.child (Outbound.request birth)) descriptor (shared born)) (sym (Outbound.descriptor birth)) logical)
   where
   captures = Captures.initialized-frontend-captures initialized path
   present = lookup-all (λ savedFrame → Capture.Valid savedFrame (shared before)) (Outbound.caller birth)
     (O.acquiring (source before)) captures (Outbound.before-PC birth)
   raw = Old.outbound-fork-facts (Outbound.caller birth) (Outbound.request birth) (Outbound.entry birth)
     (Outbound.promise birth) (Outbound.key birth) (source before) (Outbound.before-PC birth) present (Outbound.source-step birth)
   logical = subst (λ core → Facts (A.child (Outbound.request birth))
     (S.handlerStart (Outbound.entry birth) (A.socketRef (Outbound.request birth)) (Outbound.promise birth) (Outbound.key birth)) (M.world core))
     (Outbound.core-after birth) raw
